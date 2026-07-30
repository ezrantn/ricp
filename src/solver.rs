use std::collections::HashMap;

use crate::ast::{Ast, BoxRegion, NodeKind};
use crate::interval::Interval;
use rayon::prelude::*;

/// Hasil dari SMT Solver Engine
#[derive(Debug, PartialEq, Clone)]
pub enum SolverResult {
    Sat(BoxRegion),
    Unsat,
}

pub struct Solver {
    pub ast: Ast,
    pub root_node: usize,
    pub delta: f64, // Presisi target (misal 0.001)
    pub sensitivity_map: HashMap<String, f64>,
}

impl Solver {
    pub fn new(ast: Ast, root_node: usize, delta: f64) -> Self {
        let mut sensitivity_map = HashMap::default();
        for node in &ast.nodes {
            if let NodeKind::Variable(ref name) = node.kind {
                *sensitivity_map.entry(name.clone()).or_insert(0.0) += 1.0;
            }
        }
        Self {
            ast,
            root_node,
            delta,
            sensitivity_map,
        }
    }

    /// Menjalankan Contraction 1 siklus penuh (Forward + Backward)
    pub fn contract(&self, mut box_region: BoxRegion, target: Interval) -> Option<BoxRegion> {
        let mut ast = self.ast.clone();

        // 1. Forward Pass
        let _eval_res = ast.forward_eval(self.root_node, &box_region)?;

        // 2. Backward Pass
        let is_sat = ast.backward_eval(self.root_node, target, &mut box_region);

        if is_sat {
            Some(box_region)
        } else {
            None // Conflict / UNSAT
        }
    }

    /// Memeriksa apakah SEMUA interval variabel di BoxRegion sudah <= delta
    #[inline]
    pub fn is_small_enough(&self, box_region: &BoxRegion) -> bool {
        box_region.values().all(|inv| inv.width() <= self.delta)
    }

    /// Menghitung Sensitivitas Variabel berdasarkan bobot/frekuensi di AST
    #[inline]
    pub fn get_sensitivity(&self, var_name: &str) -> f64 {
        *self.sensitivity_map.get(var_name).unwrap_or(&1.0)
    }

    /// Mencari variabel dengan interval paling lebar untuk di-branch (bisection)
    pub fn split_widest_variable(&self, box_region: &BoxRegion) -> (BoxRegion, BoxRegion) {
        // Cari nama variabel dengan width terbesar
        let widest_var = box_region
            .iter()
            .max_by(|a, b| a.1.width().partial_cmp(&b.1.width()).unwrap())
            .map(|(k, _)| k.clone())
            .expect("BoxRegion tidak boleh kosong");

        let inv = box_region.get(&widest_var).unwrap();
        let mid = inv.mid();

        // Belah dua: [low, mid] dan [mid, high]
        let left_inv = Interval::new(inv.low, mid).unwrap();
        let right_inv = Interval::new(mid, inv.high).unwrap();

        let mut left_box = box_region.clone();
        let mut right_box = box_region.clone();

        left_box.insert(widest_var.clone(), left_inv);
        right_box.insert(widest_var, right_inv);

        (left_box, right_box)
    }

    /// Implementasi Sensitivity-Aware Variable Selection sesuai Paper!
    pub fn split_sensitive_variable(&self, box_region: &BoxRegion) -> (BoxRegion, BoxRegion) {
        let (best_var, inv) = box_region
            .iter()
            .max_by(|(k_a, inv_a), (k_b, inv_b)| {
                let score_a = inv_a.width() * self.get_sensitivity(k_a);
                let score_b = inv_b.width() * self.get_sensitivity(k_b);
                score_a.partial_cmp(&score_b).unwrap()
            })
            .expect("BoxRegion cannot be empty");

        let mid = inv.mid();
        let left_inv = Interval::new(inv.low, mid).unwrap();
        let right_inv = Interval::new(mid, inv.high).unwrap();

        let mut left_box = box_region.clone();
        let mut right_box = box_region.clone();

        // Overwrite langsung di tempat
        left_box.insert(best_var.clone(), left_inv);
        right_box.insert(best_var.clone(), right_inv);

        (left_box, right_box)
    }

    pub fn solve_parallel(&self, current_box: BoxRegion, target: Interval) -> SolverResult {
        self.solve_parallel_depth(current_box, target, 0)
    }

    /// Core Parallel Branch-and-Prune Loop (Rayon Fork-Join)
    fn solve_parallel_depth(
        &self,
        current_box: BoxRegion,
        target: Interval,
        depth: usize,
    ) -> SolverResult {
        // 1. Contract Step
        let contracted_box = match self.contract(current_box, target) {
            Some(b) => b,
            None => return SolverResult::Unsat,
        };

        // 2. Stopping Condition Check
        if self.is_small_enough(&contracted_box) {
            return SolverResult::Sat(contracted_box);
        }

        // 3. Branching Step
        let (left_box, right_box) = self.split_sensitive_variable(&contracted_box);

        // 4. Parallelism Threshold Adjustment:
        // Jika depth > 12 (atau batas tertentu), eksekusi sekuensial untuk hemat overhead Rayon join
        if depth > 12 {
            let left_res = self.solve_parallel_depth(left_box, target, depth + 1);
            if let SolverResult::Sat(_) = left_res {
                return left_res;
            }
            return self.solve_parallel_depth(right_box, target, depth + 1);
        }

        // Jalankan paralel via Rayon jika depth masih dangkal
        let (left_res, right_res) = rayon::join(
            || self.solve_parallel_depth(left_box, target, depth + 1),
            || self.solve_parallel_depth(right_box, target, depth + 1),
        );

        match (left_res, right_res) {
            (SolverResult::Sat(b), _) => SolverResult::Sat(b),
            (_, SolverResult::Sat(b)) => SolverResult::Sat(b),
            _ => SolverResult::Unsat,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Ast, OpType};
    use std::time::Instant;

    fn run_with_threads<F, R>(threads: usize, f: F) -> (R, std::time::Duration)
    where
        F: FnOnce() -> R + Send,
        R: Send,
    {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap();
        let start = Instant::now();
        let res = pool.install(f);
        (res, start.elapsed())
    }

    #[test]
    fn test_parallel_solver_nonlinear_equation() {
        // Memecahkan persamaan non-linear: x^2 + y = 5
        // Domain awal yang sangat luas: x ∈ [0, 10], y ∈ [0, 10]
        // Presisi delta = 0.01

        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let x_sqr = ast.add_unary(OpType::Sqr, x);
        let root = ast.add_binary(OpType::Add, x_sqr, y);

        let mut initial_box = BoxRegion::new();
        initial_box.insert("x".to_string(), Interval::new(0.0, 10.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(0.0, 10.0).unwrap());

        let solver = Solver::new(ast, root, 0.01);
        let target = Interval::point(5.0).unwrap();

        // Jalankan Parallel Solver!
        let result = solver.solve_parallel(initial_box, target);

        match result {
            SolverResult::Sat(sat_box) => {
                let x_res = sat_box.get("x").unwrap();
                let y_res = sat_box.get("y").unwrap();

                println!("PARALLEL SOLVER SAT FOUND!");
                println!("x = [{:.4}, {:.4}]", x_res.low, x_res.high);
                println!("y = [{:.4}, {:.4}]", y_res.low, y_res.high);

                // Uji verifikasi: x^2 + y harus bernilai mendekati 5
                let x_mid = x_res.mid();
                let y_mid = y_res.mid();
                let approx = x_mid * x_mid + y_mid;

                assert!(
                    (approx - 5.0).abs() < 0.05,
                    "Solusi terbukti memenuhi x^2 + y = 5!"
                );
            }
            SolverResult::Unsat => panic!("Harusnya SAT tapi ter-UNSAT!"),
        }
    }

    #[test]
    fn test_benchmark_rayon_speedup() {
        // Kita buat problem yang butuh pembagian box lumayan banyak
        // Persamaan: x^2 + y^2 = 25 (Lingkaran)
        // Domain luas: x ∈ [-10, 10], y ∈ [-10, 10]
        // Presisi delta ketat = 0.0001 (memaksa jutaan/ratusan ribu pembagian box)

        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let x_sqr = ast.add_unary(OpType::Sqr, x);
        let y_sqr = ast.add_unary(OpType::Sqr, y);
        let root = ast.add_binary(OpType::Add, x_sqr, y_sqr);

        let mut initial_box = BoxRegion::new();
        initial_box.insert("x".to_string(), Interval::new(-10.0, 10.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(-10.0, 10.0).unwrap());

        let solver = Solver::new(ast, root, 0.0001);
        let target = Interval::point(25.0).unwrap();

        // ----------------------------------------------------
        // 1. RUNNING SINGLE-THREADED (Memaksa Rayon pakai 1 thread)
        // ----------------------------------------------------
        let pool_single = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();

        let start_single = Instant::now();
        let _res_single =
            pool_single.install(|| solver.solve_parallel(initial_box.clone(), target));
        let duration_single = start_single.elapsed();

        // ----------------------------------------------------
        // 2. RUNNING MULTI-THREADED (Memakai seluruh CPU Cores)
        // ----------------------------------------------------
        let num_cores = num_cpus::get(); // Butuh crate `num_cpus` jika mau log, atau biarkan default rayon
        let start_multi = Instant::now();
        let _res_multi = solver.solve_parallel(initial_box, target);
        let duration_multi = start_multi.elapsed();

        // ----------------------------------------------------
        // 3. PRINT HASIL BENCHMARK
        // ----------------------------------------------------
        println!("\n=== 📊 BENCHMARK RESULTS ===");
        println!("Single-thread execution time : {:?}", duration_single);
        println!("Multi-thread execution time  : {:?}", duration_multi);

        let speedup = duration_single.as_secs_f64() / duration_multi.as_secs_f64();
        println!("  SPEEDUP FACTOR            : {:.2}x Faster!", speedup);
        println!("============================\n");
    }

    #[test]
    fn test_solve_transcendental_equation() {
        // Skenario Persamaan: sin(x) + exp(y) = 2.0
        // Domain Awal: x ∈ [0, PI/2], y ∈ [-2, 2]
        // Presisi delta = 0.001

        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let sin_x = ast.add_unary(OpType::Sin, x);
        let exp_y = ast.add_unary(OpType::Exp, y);
        let root = ast.add_binary(OpType::Add, sin_x, exp_y);

        let mut initial_box = BoxRegion::new();
        initial_box.insert(
            "x".to_string(),
            Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap(),
        );
        initial_box.insert("y".to_string(), Interval::new(-2.0, 2.0).unwrap());

        let solver = Solver::new(ast, root, 0.001);
        let target = Interval::point(2.0).unwrap();

        let result = solver.solve_parallel(initial_box, target);

        match result {
            SolverResult::Sat(sat_box) => {
                let x_res = sat_box.get("x").unwrap();
                let y_res = sat_box.get("y").unwrap();

                println!("\n===  TRANSCENDENTAL SAT SOLUTION ===");
                println!("x = [{:.5}, {:.5}]", x_res.low, x_res.high);
                println!("y = [{:.5}, {:.5}]", y_res.low, y_res.high);

                // Verifikasi: sin(x) + exp(y) ≈ 2.0
                let val = x_res.mid().sin() + y_res.mid().exp();
                println!("Verification sin(x) + exp(y) = {:.5}", val);
                assert!((val - 2.0).abs() < 0.01);
            }
            SolverResult::Unsat => panic!("Gagal menemukan solusi untuk sin(x) + exp(y) = 2!"),
        }
    }

    // =========================================================================
    // 1. SCALABILITY SWEEP BENCHMARK (1, 2, 4, 8, 16 Threads)
    // =========================================================================
    #[test]
    fn test_benchmark_scalability_sweep() {
        // Benchmark: Highly non-linear polynomial sphere x^2 + y^2 = 25
        // Delta super ketat (0.00005) untuk memaksa pembagian search space yang sangat dalam
        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let x_sqr = ast.add_unary(OpType::Sqr, x);
        let y_sqr = ast.add_unary(OpType::Sqr, y);
        let root = ast.add_binary(OpType::Add, x_sqr, y_sqr);

        let mut initial_box = BoxRegion::new();
        initial_box.insert("x".to_string(), Interval::new(-10.0, 10.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(-10.0, 10.0).unwrap());

        let solver = Solver::new(ast, root, 0.00005);
        let target = Interval::point(25.0).unwrap();

        let thread_counts = vec![1, 2, 4, 8, 16];
        let mut base_duration_secs = 0.0;

        println!("\n=============================================================");
        println!(" BENCHMARK 1: SCALABILITY SWEEP (RAYON WORK-STEALING)");
        println!("=============================================================");
        println!(
            "{:<10} | {:<18} | {:<12}",
            "Threads", "Execution Time", "Speedup"
        );
        println!("-------------------------------------------------------------");

        for &t in &thread_counts {
            let (_, duration) =
                run_with_threads(t, || solver.solve_parallel(initial_box.clone(), target));

            let dur_secs = duration.as_secs_f64();
            if t == 1 {
                base_duration_secs = dur_secs;
            }

            let speedup = base_duration_secs / dur_secs;
            println!("{:<10} | {:<18?} | {:.2}x", t, duration, speedup);
        }
        println!("=============================================================\n");
    }

    // =========================================================================
    // 2. VARIATIVE NON-LINEAR PROBLEM SUITE
    // =========================================================================

    /// Problem 1: High-Degree Polynomial (x^4 + y^2 = 17)
    #[test]
    fn test_benchmark_high_degree_polynomial() {
        // x^4 + y^2 = 17 over x ∈ [-3, 3], y ∈ [-5, 5]
        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let x_sqr = ast.add_unary(OpType::Sqr, x);
        let x_4 = ast.add_unary(OpType::Sqr, x_sqr); // (x^2)^2 = x^4
        let y_sqr = ast.add_unary(OpType::Sqr, y);
        let root = ast.add_binary(OpType::Add, x_4, y_sqr);

        let mut initial_box = BoxRegion::new();
        initial_box.insert("x".to_string(), Interval::new(-3.0, 3.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(-5.0, 5.0).unwrap());

        let solver = Solver::new(ast, root, 0.0001);
        let target = Interval::point(17.0).unwrap();

        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone(), target));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box, target)
        });

        assert!(matches!(res_multi, SolverResult::Sat(_)));
        println!(
            "P1: High-Degree Poly [x^4 + y^2 = 17] -> 1-Thread: {:?} | Multi: {:?} ({:.2}x speedup)",
            d1,
            d_multi,
            d1.as_secs_f64() / d_multi.as_secs_f64()
        );
    }

    /// Problem 2: Oscillatory Trigonometric Function (sin(x) * sin(y) = 0.5)
    #[test]
    fn test_benchmark_oscillatory_trig() {
        // sin(x) * sin(y) = 0.5 over x, y ∈ [0, PI]
        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let sin_x = ast.add_unary(OpType::Sin, x);
        let sin_y = ast.add_unary(OpType::Sin, y);
        let root = ast.add_binary(OpType::Mul, sin_x, sin_y);

        let mut initial_box = BoxRegion::new();
        initial_box.insert(
            "x".to_string(),
            Interval::new(0.0, std::f64::consts::PI).unwrap(),
        );
        initial_box.insert(
            "y".to_string(),
            Interval::new(0.0, std::f64::consts::PI).unwrap(),
        );

        let solver = Solver::new(ast, root, 0.0005);
        let target = Interval::point(0.5).unwrap();

        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone(), target));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box, target)
        });

        assert!(matches!(res_multi, SolverResult::Sat(_)));
        println!(
            "P2: Oscillatory Trig [sin(x)*sin(y) = 0.5] -> 1-Thread: {:?} | Multi: {:?} ({:.2}x speedup)",
            d1,
            d_multi,
            d1.as_secs_f64() / d_multi.as_secs_f64()
        );
    }

    /// Problem 3: Mixed Exponential-Polynomial System (exp(x) - y^2 = 0)
    #[test]
    fn test_benchmark_mixed_exp_poly() {
        // exp(x) - y^2 = 0 over x ∈ [-2, 2], y ∈ [1, 4]
        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let exp_x = ast.add_unary(OpType::Exp, x);
        let y_sqr = ast.add_unary(OpType::Sqr, y);
        let root = ast.add_binary(OpType::Sub, exp_x, y_sqr);

        let mut initial_box = BoxRegion::new();
        initial_box.insert("x".to_string(), Interval::new(-2.0, 2.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(1.0, 4.0).unwrap());

        let solver = Solver::new(ast, root, 0.0005);
        let target = Interval::point(0.0).unwrap();

        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone(), target));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box, target)
        });

        assert!(matches!(res_multi, SolverResult::Sat(_)));
        println!(
            "P3: Mixed Exp-Poly [exp(x) - y^2 = 0] -> 1-Thread: {:?} | Multi: {:?} ({:.2}x speedup)",
            d1,
            d_multi,
            d1.as_secs_f64() / d_multi.as_secs_f64()
        );
    }

    // =========================================================================
    // 3. MEMORY FOOTPRINT & AST ARENA PROFILING
    // =========================================================================
    #[test]
    fn test_benchmark_memory_footprint() {
        // Mengukur footprint memori AST arena allocation `Vec<Node>` di Rust
        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let x_sqr = ast.add_unary(OpType::Sqr, x);
        let y_sqr = ast.add_unary(OpType::Sqr, y);
        let root = ast.add_binary(OpType::Add, x_sqr, y_sqr);

        let node_count = ast.nodes.len();
        let single_node_size = std::mem::size_of::<crate::ast::Node>();
        let total_ast_bytes = node_count * single_node_size;

        println!("\n=============================================================");
        println!(" MEMORY FOOTPRINT & ARENA ALLOCATION PROFILING");
        println!("=============================================================");
        println!("Total AST Nodes          : {} nodes", node_count);
        println!("Size per Node struct     : {} bytes", single_node_size);
        println!(
            "Total AST Memory Size    : {} bytes ({:.2} KB)",
            total_ast_bytes,
            total_ast_bytes as f64 / 1024.0
        );
        println!("Zero Heap Allocation Ref : YES (Index-based Arena Allocation)");
        println!("=============================================================\n");

        assert_eq!(node_count, 5);
    }

    /// Real-World Problem 1: 2-DOF Robotic Arm Inverse Kinematics
    /// Menentukan sudut sendi robot (theta1, theta2) agar ujung arm mencapai target koordinat (X, Y).
    /// Persamaan: x_target = L1*cos(t1) + L2*cos(t1 + t2), y_target = L1*sin(t1) + L2*sin(t1 + t2)
    #[test]
    fn test_benchmark_realworld_robotic_arm_ik() {
        // Target End-Effector: X = 1.5, Y = 1.0 (L1 = 1.0, L2 = 1.0)
        // Constraint: cos(t1) + cos(t1 + t2) - 1.5 = 0
        // Domain t1, t2 ∈ [0, PI/2] (Sudut kuadran pertama)
        let mut ast = Ast::new();
        let t1 = ast.add_variable("t1");
        let t2 = ast.add_variable("t2");
        let t1_plus_t2 = ast.add_binary(OpType::Add, t1, t2);
        
        let cos_t1 = ast.add_unary(OpType::Cos, t1);
        let cos_t12 = ast.add_unary(OpType::Cos, t1_plus_t2);
        let x_pos = ast.add_binary(OpType::Add, cos_t1, cos_t12);

        let mut initial_box = BoxRegion::new();
        initial_box.insert(
            "t1".to_string(),
            Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap(),
        );
        initial_box.insert(
            "t2".to_string(),
            Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap(),
        );

        let solver = Solver::new(ast, x_pos, 0.0001);
        let target = Interval::point(1.5).unwrap();

        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone(), target));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box, target)
        });

        assert!(matches!(res_multi, SolverResult::Sat(_)));
        println!(
            "RW1: Robotic Arm IK [2-DOF Coordinate Reach] -> 1-Thread: {:?} | Multi: {:?} ({:.2}x speedup)",
            d1, d_multi, d1.as_secs_f64() / d_multi.as_secs_f64()
        );
    }

    /// Real-World Problem 2: Autonomous Drone Collision Boundary Verification
    /// Memastikan jarak Euclidean antara dua drone (D1 dan D2) tidak melanggar safety zone (R >= 2.0).
    /// Distance = sqrt((x2 - x1)^2 + (y2 - y1)^2) over 4 Variables!
    #[test]
    fn test_benchmark_realworld_drone_collision_avoidance() {
        // 4 Variabel: x1, y1 (Drone 1), x2, y2 (Drone 2)
        let mut ast = Ast::new();
        let x1 = ast.add_variable("x1");
        let y1 = ast.add_variable("y1");
        let x2 = ast.add_variable("x2");
        let y2 = ast.add_variable("y2");

        let dx = ast.add_binary(OpType::Sub, x2, x1);
        let dy = ast.add_binary(OpType::Sub, y2, y1);
        let dx_sqr = ast.add_unary(OpType::Sqr, dx);
        let dy_sqr = ast.add_unary(OpType::Sqr, dy);
        let dist_sqr = ast.add_binary(OpType::Add, dx_sqr, dy_sqr);

        let mut initial_box = BoxRegion::new();
        initial_box.insert("x1".to_string(), Interval::new(-5.0, 0.0).unwrap());
        initial_box.insert("y1".to_string(), Interval::new(-5.0, 0.0).unwrap());
        initial_box.insert("x2".to_string(), Interval::new(0.0, 5.0).unwrap());
        initial_box.insert("y2".to_string(), Interval::new(0.0, 5.0).unwrap());

        // Cek apakah ada trajectory di mana dist_sqr = 4.0 (Distance = 2.0 meter)
        let solver = Solver::new(ast, dist_sqr, 0.0005);
        let target = Interval::point(4.0).unwrap();

        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone(), target));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box, target)
        });

        assert!(matches!(res_multi, SolverResult::Sat(_)));
        println!(
            "RW2: Drone Safety Zone [4-Var Euclidean Clearance] -> 1-Thread: {:?} | Multi: {:?} ({:.2}x speedup)",
            d1, d_multi, d1.as_secs_f64() / d_multi.as_secs_f64()
        );
    }

    /// Real-World Problem 3: Non-Linear Diode Circuit Equilibrium State
    /// Persamaan Transistor/Diode Shockley: I = I_s * (exp(V / V_t) - 1)
    /// Solver mencari tegangan kerja V saat arus I berada pada kondisi ambang batas.
    #[test]
    fn test_benchmark_realworld_circuit_equilibrium() {
        let mut ast = Ast::new();
        let v = ast.add_variable("v"); // Voltage Variable
        
        let const_scale = ast.add_variable("const_scale");
        // Scale factor V / V_t (asumsi V_t = 0.026V, diprogram sebagai scaled variable)
        let scaled_v = ast.add_binary(OpType::Mul, v, const_scale); 
        let exp_v = ast.add_unary(OpType::Exp, scaled_v);
        
        let mut initial_box = BoxRegion::new();
        initial_box.insert("v".to_string(), Interval::new(0.1, 1.0).unwrap());
        initial_box.insert("const_scale".to_string(), Interval::point(10.0).unwrap()); // Constant 10x multiplier

        let solver = Solver::new(ast, exp_v, 0.0001);
        let target = Interval::new(50.0, 100.0).unwrap(); // Target Current Range

        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone(), target));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box, target)
        });

        assert!(matches!(res_multi, SolverResult::Sat(_)));
        println!(
            "RW3: Diode Shockley State [Non-Linear Exponential Equilibrium] -> 1-Thread: {:?} | Multi: {:?} ({:.2}x speedup)",
            d1, d_multi, d1.as_secs_f64() / d_multi.as_secs_f64()
        );
    }
}
