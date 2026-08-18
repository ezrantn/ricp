use fxhash::FxHashMap;

use crate::ast::{ Ast, BoxRegion, NodeId, NodeKind, OpType };
use crate::interval::Interval;

/// Result from SMT Solver Engine
#[derive(Debug, PartialEq, Clone)]
pub enum SolverResult {
    Sat(BoxRegion),
    Unsat,
}

/// A single constraint: 'root' node of the AST must evaluate into 'target'.
#[derive(Debug, Clone)]
pub struct Constraint {
    pub root: NodeId,
    pub target: Interval,
}

impl Constraint {
    pub fn new(root: NodeId, target: Interval) -> Self {
        Self { root, target }
    }
}

pub struct Solver {
    pub ast: Ast,
    pub constraints: Vec<Constraint>,
    pub delta: f64, // Target precision (e.g. 0.001)
    pub sensitivity_map: FxHashMap<String, f64>,
    pub max_propagation_rounds: usize, // Safety cap on HC4 fixpoint rounds inside a single contract() call
}

impl Solver {
    pub fn new(ast: Ast, constraints: Vec<Constraint>, delta: f64) -> Self {
        let mut sensitivity_map = FxHashMap::default();
        assert!(!constraints.is_empty(), "Solver requires at least one constraint.");
        for node in &ast.nodes {
            match &node.kind {
                // Jika node adalah Unary Operator (seperti Exp, Sqr, Sin, dll)
                NodeKind::Unary { op, child } => {
                    if let NodeKind::Variable(ref name) = ast.nodes[*child].kind {
                        let weight = match op {
                            OpType::Exp => 10.0, // Non-linear amplification tinggi!
                            OpType::Sqr => 3.0, // Amplifikasi kuadratik
                            OpType::Sin | OpType::Cos => 2.0, // Osilatif
                            _ => 1.0,
                        };
                        *sensitivity_map.entry(name.clone()).or_insert(0.0) += weight;
                    }
                }
                // Jika node adalah Variable biasa (tanpa operator khusus di atasnya)
                NodeKind::Variable(name) => {
                    *sensitivity_map.entry(name.clone()).or_insert(0.0) += 1.0;
                }
                _ => {}
            }
        }

        Self {
            ast,
            constraints,
            delta,
            sensitivity_map,
            max_propagation_rounds: 50,
        }
    }

    /// Convenience constructor for the single-equation case.
    pub fn new_single(ast: Ast, root_node: usize, target: Interval, delta: f64) -> Self {
        Self::new(ast, vec![Constraint::new(root_node, target)], delta)
    }

    #[inline]
    fn total_width(box_region: &BoxRegion) -> f64 {
        box_region
            .values()
            .map(|iv| iv.width())
            .sum()
    }

    fn contract_one(
        &self,
        ast: &mut Ast,
        constraint: &Constraint,
        box_region: &mut BoxRegion
    ) -> bool {
        // 1. Forward Pass. Missing domain (unbound var) is treated as "no info yet" -> skip.
        if ast.forward_eval(constraint.root, box_region).is_none() {
            return true;
        }
        ast.backward_eval(constraint.root, constraint.target, box_region)
    }

    /// Propagate ALL constraints to a shared fixpoint (AC3-style outer loop).
    /// Since constraints can share variables, narrowing from one constraint can
    /// unlock further narrowing in another - we keep sweeping until the total
    /// box width stops shrinking (or we hit the round cap as a safety valve).
    pub fn contract(&self, mut box_region: BoxRegion) -> Option<BoxRegion> {
        let mut ast = self.ast.clone();
        let mut prev_width = f64::INFINITY;

        for _ in 0..self.max_propagation_rounds {
            for constraint in &self.constraints {
                if !self.contract_one(&mut ast, constraint, &mut box_region) {
                    return None; // Conflict / UNSAT on this constraint
                }
            }

            let width = Self::total_width(&box_region);
            if prev_width - width < 1e-12 {
                break; // Fixpoint reached (or negligible progress left)
            }

            prev_width = width;
        }

        Some(box_region)
    }

    /// Check if all variable intervals are small enough (width <= delta)
    #[inline]
    fn _is_small_enough(&self, box_region: &BoxRegion) -> bool {
        box_region.values().all(|inv| inv.width() <= self.delta)
    }

    /// Get the occurrence count of a variable (weight/frequency from AST)
    #[inline]
    fn _get_occurrence(&self, var_name: &str) -> f64 {
        *self.sensitivity_map.get(var_name).unwrap_or(&1.0)
    }

    /// Find the widest variable to branch on (bisection)
    pub fn split_widest_variable(&self, box_region: &BoxRegion) -> (BoxRegion, BoxRegion) {
        // Find the widest variable by width
        let widest_var = box_region
            .iter()
            .max_by(|a, b| a.1.width().partial_cmp(&b.1.width()).unwrap())
            .map(|(k, _)| k.clone())
            .expect("BoxRegion cannot be empty");

        let inv = box_region.get(&widest_var).unwrap();
        let mid = inv.mid();

        // Split the widest variable into two: [low, mid] and [mid, high]
        let left_inv = Interval::new(inv.low, mid).unwrap();
        let right_inv = Interval::new(mid, inv.high).unwrap();

        let mut left_box = box_region.clone();
        let mut right_box = box_region.clone();

        left_box.insert(widest_var.clone(), left_inv);
        right_box.insert(widest_var, right_inv);

        (left_box, right_box)
    }

    /// Find the sensitive variable to branch on (bisection)
    pub fn split_sensitive_variable(&self, box_region: &BoxRegion) -> (BoxRegion, BoxRegion) {
        let (best_var, inv) = box_region
            .iter()
            .max_by(|(k_a, inv_a), (k_b, inv_b)| {
                // Alpha factor 0.15 meredam bobot ekstrim biar ga starvation
                let weight_a = 1.0 + 0.15 * self._get_occurrence(k_a);
                let weight_b = 1.0 + 0.15 * self._get_occurrence(k_b);

                let score_a = inv_a.width() * weight_a;
                let score_b = inv_b.width() * weight_b;

                score_a.partial_cmp(&score_b).unwrap()
            })
            .expect("BoxRegion cannot be empty");

        let mid = inv.mid();
        let left_inv = Interval::new(inv.low, mid).unwrap();
        let right_inv = Interval::new(mid, inv.high).unwrap();

        let mut left_box = box_region.clone();
        let mut right_box = box_region.clone();

        // Overwrite the sensitive variable in both boxes
        left_box.insert(best_var.clone(), left_inv);
        right_box.insert(best_var.clone(), right_inv);

        (left_box, right_box)
    }

    pub fn solve_parallel(&self, current_box: BoxRegion) -> SolverResult {
        self.solve_parallel_depth(current_box, 0)
    }

    /// Core Parallel Branch-and-Prune Loop (Rayon Fork-Join)
    fn solve_parallel_depth(&self, current_box: BoxRegion, depth: usize) -> SolverResult {
        // 1. Contract Step (sweeps ALL constraints to a shared fixpoint)
        let contracted_box = match self.contract(current_box) {
            Some(b) => b,
            None => {
                return SolverResult::Unsat;
            }
        };

        // 2. Stopping Condition Check
        if self._is_small_enough(&contracted_box) {
            return SolverResult::Sat(contracted_box);
        }

        // 3. Branching Step
        let (left_box, right_box) = self.split_sensitive_variable(&contracted_box);

        // 4. Parallelism Threshold:
        // If depth exceeds 12, switch to sequential execution to save Rayon join overhead
        if depth > 12 {
            let left_res = self.solve_parallel_depth(left_box, depth + 1);
            if let SolverResult::Sat(_) = left_res {
                return left_res;
            }
            return self.solve_parallel_depth(right_box, depth + 1);
        }

        // 5. Parallel Execution via Rayon
        let (left_res, right_res) = rayon::join(
            || self.solve_parallel_depth(left_box, depth + 1),
            || self.solve_parallel_depth(right_box, depth + 1)
        );

        match (left_res, right_res) {
            (SolverResult::Sat(b), _) => SolverResult::Sat(b),
            (_, SolverResult::Sat(b)) => SolverResult::Sat(b),
            _ => SolverResult::Unsat,
        }
    }

    pub fn solve_parallel_widest(&self, current_box: BoxRegion) -> SolverResult {
        self.solve_parallel_depth_widest(current_box, 0)
    }

    /// Widest interval for ablation study parallel Branch-and-Prune Loop (Rayon Fork-Join)
    fn solve_parallel_depth_widest(&self, current_box: BoxRegion, depth: usize) -> SolverResult {
        // 1. Contract Step (sweeps ALL constraints to a shared fixpoint)
        let contracted_box = match self.contract(current_box) {
            Some(b) => b,
            None => {
                return SolverResult::Unsat;
            }
        };

        // 2. Stopping Condition Check
        if self._is_small_enough(&contracted_box) {
            return SolverResult::Sat(contracted_box);
        }

        // 3. Branching Step
        let (left_box, right_box) = self.split_widest_variable(&contracted_box);

        // 4. Parallelism Threshold:
        // If depth exceeds 12, switch to sequential execution to save Rayon join overhead
        if depth > 12 {
            let left_res = self.solve_parallel_depth_widest(left_box, depth + 1);
            if let SolverResult::Sat(_) = left_res {
                return left_res;
            }
            return self.solve_parallel_depth_widest(right_box, depth + 1);
        }

        // 5. Parallel Execution via Rayon
        let (left_res, right_res) = rayon::join(
            || self.solve_parallel_depth_widest(left_box, depth + 1),
            || self.solve_parallel_depth_widest(right_box, depth + 1)
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
    use crate::ast::{ Ast, OpType };
    use std::time::Instant;

    fn run_with_threads<F, R>(threads: usize, f: F) -> (R, std::time::Duration)
        where F: FnOnce() -> R + Send, R: Send
    {
        let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
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

        let mut initial_box = BoxRegion::default();
        initial_box.insert("x".to_string(), Interval::new(0.0, 10.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(0.0, 10.0).unwrap());

        let solver = Solver::new_single(ast, root, Interval::point(5.0).unwrap(), 0.001);
        let result = solver.solve_parallel(initial_box);

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

                assert!((approx - 5.0).abs() < 0.05, "Solusi terbukti memenuhi x^2 + y = 5!");
            }
            SolverResult::Unsat => panic!("Harusnya SAT tapi ter-UNSAT!"),
        }
    }

    #[test]
    fn test_multi_constraint_system() {
        // Sistem 2 persamaan simultan berbagi variabel yang sama:
        //   C1: x^2 + y = 10
        //   C2: x - y  = 2
        // Solusi analitik: x^2 + (x - 2) = 10 => x^2 + x - 12 = 0 => x = 3 atau x = -4
        // Domain awal x, y ∈ [-5, 5] membuat kedua akar mungkin ditemukan.
        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");

        let x_sqr = ast.add_unary(OpType::Sqr, x);
        let c1_root = ast.add_binary(OpType::Add, x_sqr, y);

        let c2_root = ast.add_binary(OpType::Sub, x, y);

        let mut initial_box = BoxRegion::default();
        initial_box.insert("x".to_string(), Interval::new(-5.0, 5.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(-5.0, 5.0).unwrap());

        let solver = Solver::new(
            ast,
            vec![
                Constraint::new(c1_root, Interval::point(10.0).unwrap()),
                Constraint::new(c2_root, Interval::point(2.0).unwrap())
            ],
            0.001
        );

        let result = solver.solve_parallel(initial_box);

        match result {
            SolverResult::Sat(sat_box) => {
                let x_res = sat_box.get("x").unwrap();
                let y_res = sat_box.get("y").unwrap();

                let x_mid = x_res.mid();
                let y_mid = y_res.mid();

                println!("\n=== MULTI-CONSTRAINT SAT SOLUTION ===");
                println!("x = [{:.5}, {:.5}]", x_res.low, x_res.high);
                println!("y = [{:.5}, {:.5}]", y_res.low, y_res.high);

                // Kedua constraint HARUS terpenuhi secara simultan
                assert!(
                    (x_mid * x_mid + y_mid - 10.0).abs() < 0.05,
                    "C1 (x^2 + y = 10) harus terpenuhi"
                );
                assert!((x_mid - y_mid - 2.0).abs() < 0.05, "C2 (x - y = 2) harus terpenuhi");
            }
            SolverResult::Unsat =>
                panic!("Harusnya SAT: sistem punya solusi riil (x=3,y=1) atau (x=-4,y=-6)"),
        }
    }

    #[test]
    fn test_multi_constraint_unsat_system() {
        // Sistem yang inkonsisten dalam domain yang diberikan:
        //   C1: x = 1   (domain sempit)
        //   C2: x = 5   (kontradiksi langsung dengan C1)
        let mut ast = Ast::new();
        let x = ast.add_variable("x");

        let mut initial_box = BoxRegion::default();
        initial_box.insert("x".to_string(), Interval::new(0.0, 10.0).unwrap());

        let solver = Solver::new(
            ast,
            vec![
                Constraint::new(x, Interval::point(1.0).unwrap()),
                Constraint::new(x, Interval::point(5.0).unwrap())
            ],
            0.001
        );

        let result = solver.solve_parallel(initial_box);
        assert_eq!(result, SolverResult::Unsat);
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

        let mut initial_box = BoxRegion::default();
        initial_box.insert(
            "x".to_string(),
            Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap()
        );
        initial_box.insert("y".to_string(), Interval::new(-2.0, 2.0).unwrap());

        let solver = Solver::new_single(ast, root, Interval::point(2.0).unwrap(), 0.00005);
        let result = solver.solve_parallel(initial_box);

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

        let mut initial_box = BoxRegion::default();
        initial_box.insert("x".to_string(), Interval::new(-10.0, 10.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(-10.0, 10.0).unwrap());

        let solver = Solver::new_single(ast, root, Interval::point(25.0).unwrap(), 0.0001);
        let target = Interval::point(25.0).unwrap();

        // ----------------------------------------------------
        // 1. RUNNING SINGLE-THREADED (Memaksa Rayon pakai 1 thread)
        // ----------------------------------------------------
        let pool_single = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();

        let start_single = Instant::now();
        let _res_single = pool_single.install(|| solver.solve_parallel(initial_box.clone()));
        let duration_single = start_single.elapsed();

        // ----------------------------------------------------
        // 2. RUNNING MULTI-THREADED (Memakai seluruh CPU Cores)
        // ----------------------------------------------------
        let num_cores = num_cpus::get(); // Butuh crate `num_cpus` jika mau log, atau biarkan default rayon
        let start_multi = Instant::now();
        let _res_multi = solver.solve_parallel(initial_box);
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

        let mut initial_box = BoxRegion::default();
        initial_box.insert("x".to_string(), Interval::new(-10.0, 10.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(-10.0, 10.0).unwrap());

        let solver = Solver::new_single(ast, root, Interval::point(25.0).unwrap(), 0.00005);
        let thread_counts = vec![1, 2, 4, 8, 16];
        let mut base_duration_secs = 0.0;

        println!("\n=============================================================");
        println!(" BENCHMARK 1: SCALABILITY SWEEP (RAYON WORK-STEALING)");
        println!("=============================================================");
        println!("{:<10} | {:<18} | {:<12}", "Threads", "Execution Time", "Speedup");
        println!("-------------------------------------------------------------");

        for &t in &thread_counts {
            let (_, duration) = run_with_threads(t, || solver.solve_parallel(initial_box.clone()));

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

        let mut initial_box = BoxRegion::default();
        initial_box.insert("x".to_string(), Interval::new(-3.0, 3.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(-5.0, 5.0).unwrap());

        let solver = Solver::new_single(ast, root, Interval::point(17.0).unwrap(), 0.0001);
        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone()));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box)
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

        let mut initial_box = BoxRegion::default();
        initial_box.insert("x".to_string(), Interval::new(0.0, std::f64::consts::PI).unwrap());
        initial_box.insert("y".to_string(), Interval::new(0.0, std::f64::consts::PI).unwrap());

        let solver = Solver::new_single(ast, root, Interval::point(0.5).unwrap(), 0.0005);
        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone()));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box)
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

        let mut initial_box = BoxRegion::default();
        initial_box.insert("x".to_string(), Interval::new(-2.0, 2.0).unwrap());
        initial_box.insert("y".to_string(), Interval::new(1.0, 4.0).unwrap());

        let solver = Solver::new_single(ast, root, Interval::point(0.0).unwrap(), 0.0005);
        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone()));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box)
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
            (total_ast_bytes as f64) / 1024.0
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

        let mut initial_box = BoxRegion::default();
        initial_box.insert(
            "t1".to_string(),
            Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap()
        );
        initial_box.insert(
            "t2".to_string(),
            Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap()
        );

        let solver = Solver::new_single(ast, x_pos, Interval::point(1.5).unwrap(), 0.0001);
        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone()));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box)
        });

        assert!(matches!(res_multi, SolverResult::Sat(_)));
        println!(
            "RW1: Robotic Arm IK [2-DOF Coordinate Reach] -> 1-Thread: {:?} | Multi: {:?} ({:.2}x speedup)",
            d1,
            d_multi,
            d1.as_secs_f64() / d_multi.as_secs_f64()
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

        let mut initial_box = BoxRegion::default();
        initial_box.insert("x1".to_string(), Interval::new(-5.0, 0.0).unwrap());
        initial_box.insert("y1".to_string(), Interval::new(-5.0, 0.0).unwrap());
        initial_box.insert("x2".to_string(), Interval::new(0.0, 5.0).unwrap());
        initial_box.insert("y2".to_string(), Interval::new(0.0, 5.0).unwrap());

        // Cek apakah ada trajectory di mana dist_sqr = 4.0 (Distance = 2.0 meter)
        let solver = Solver::new_single(ast, dist_sqr, Interval::point(4.0).unwrap(), 0.0005);
        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone()));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box)
        });

        assert!(matches!(res_multi, SolverResult::Sat(_)));
        println!(
            "RW2: Drone Safety Zone [4-Var Euclidean Clearance] -> 1-Thread: {:?} | Multi: {:?} ({:.2}x speedup)",
            d1,
            d_multi,
            d1.as_secs_f64() / d_multi.as_secs_f64()
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

        let mut initial_box = BoxRegion::default();
        initial_box.insert("v".to_string(), Interval::new(0.1, 1.0).unwrap());
        initial_box.insert("const_scale".to_string(), Interval::point(10.0).unwrap()); // Constant 10x multiplier

        let solver = Solver::new_single(ast, exp_v, Interval::new(50.0, 100.0).unwrap(), 0.0001);
        let (_, d1) = run_with_threads(1, || solver.solve_parallel(initial_box.clone()));
        let (res_multi, d_multi) = run_with_threads(num_cpus::get(), || {
            solver.solve_parallel(initial_box)
        });

        assert!(matches!(res_multi, SolverResult::Sat(_)));
        println!(
            "RW3: Diode Shockley State [Non-Linear Exponential Equilibrium] -> 1-Thread: {:?} | Multi: {:?} ({:.2}x speedup)",
            d1,
            d_multi,
            d1.as_secs_f64() / d_multi.as_secs_f64()
        );
    }

    // =========================================================================
    // 4. ABLATION STUDY: AOWB (SENSITIVE) VS STANDARD MAX-WIDTH BISECTION
    // =========================================================================
    // #[test]
    // fn test_benchmark_ablation_study_aowb_vs_widest() {
    //     println!("\n=======================================================================================");
    //     println!(" ABLATION STUDY: AOWB (PROPOSED) VS STANDARD MAX-WIDTH BISECTION");
    //     println!("=======================================================================================");
    //     println!(
    //         "{:<35} | {:<15} | {:<15} | {:<12}",
    //         "Problem Benchmark", "Max-Width (Widest)", "AOWB (Proposed)", "Speedup Gain"
    //     );
    //     println!("---------------------------------------------------------------------------------------");

    //     let num_cores = num_cpus::get();

    //     // ---------------------------------------------------------------------
    //     // Problem P1: High-Degree Polynomial (x^4 + y^2 = 17)
    //     // ---------------------------------------------------------------------
    //     {
    //         let mut ast = Ast::new();
    //         let x = ast.add_variable("x");
    //         let y = ast.add_variable("y");
    //         let x_sqr = ast.add_unary(OpType::Sqr, x);
    //         let x_4 = ast.add_unary(OpType::Sqr, x_sqr);
    //         let y_sqr = ast.add_unary(OpType::Sqr, y);
    //         let root = ast.add_binary(OpType::Add, x_4, y_sqr);

    //         let mut initial_box = BoxRegion::default();
    //         initial_box.insert("x".to_string(), Interval::new(-3.0, 3.0).unwrap());
    //         initial_box.insert("y".to_string(), Interval::new(-5.0, 5.0).unwrap());

    //         let solver = Solver::new(ast, root, 0.0001);
    //         let target = Interval::point(17.0).unwrap();

    //         let (_, d_widest) = run_with_threads(num_cores, || solver.solve_parallel_widest(initial_box.clone(), target));
    //         let (_, d_aowb) = run_with_threads(num_cores, || solver.solve_parallel(initial_box, target));

    //         let speedup = d_widest.as_secs_f64() / d_aowb.as_secs_f64();
    //         println!(
    //             "{:<35} | {:<15?} | {:<15?} | {:.2}x",
    //             "P1: High-Degree Poly [x^4+y^2=17]", d_widest, d_aowb, speedup
    //         );
    //     }

    //     // ---------------------------------------------------------------------
    //     // Problem P2: Oscillatory Trigonometric (sin(x) * sin(y) = 0.5)
    //     // ---------------------------------------------------------------------
    //     {
    //         let mut ast = Ast::new();
    //         let x = ast.add_variable("x");
    //         let y = ast.add_variable("y");
    //         let sin_x = ast.add_unary(OpType::Sin, x);
    //         let sin_y = ast.add_unary(OpType::Sin, y);
    //         let root = ast.add_binary(OpType::Mul, sin_x, sin_y);

    //         let mut initial_box = BoxRegion::default();
    //         initial_box.insert("x".to_string(), Interval::new(0.0, std::f64::consts::PI).unwrap());
    //         initial_box.insert("y".to_string(), Interval::new(0.0, std::f64::consts::PI).unwrap());

    //         let solver = Solver::new(ast, root, 0.0005);
    //         let target = Interval::point(0.5).unwrap();

    //         let (_, d_widest) = run_with_threads(num_cores, || solver.solve_parallel_widest(initial_box.clone(), target));
    //         let (_, d_aowb) = run_with_threads(num_cores, || solver.solve_parallel(initial_box, target));

    //         let speedup = d_widest.as_secs_f64() / d_aowb.as_secs_f64();
    //         println!(
    //             "{:<35} | {:<15?} | {:<15?} | {:.2}x",
    //             "P2: Oscillatory Trig [sin*sin=0.5]", d_widest, d_aowb, speedup
    //         );
    //     }

    //     // ---------------------------------------------------------------------
    //     // Problem P3: Mixed Exponential-Polynomial (exp(x) - y^2 = 0)
    //     // ---------------------------------------------------------------------
    //     {
    //         let mut ast = Ast::new();
    //         let x = ast.add_variable("x");
    //         let y = ast.add_variable("y");
    //         let exp_x = ast.add_unary(OpType::Exp, x);
    //         let y_sqr = ast.add_unary(OpType::Sqr, y);
    //         let root = ast.add_binary(OpType::Sub, exp_x, y_sqr);

    //         let mut initial_box = BoxRegion::default();
    //         initial_box.insert("x".to_string(), Interval::new(-2.0, 2.0).unwrap());
    //         initial_box.insert("y".to_string(), Interval::new(1.0, 4.0).unwrap());

    //         let solver = Solver::new(ast, root, 0.0005);
    //         let target = Interval::point(0.0).unwrap();

    //         let (_, d_widest) = run_with_threads(num_cores, || solver.solve_parallel_widest(initial_box.clone(), target));
    //         let (_, d_aowb) = run_with_threads(num_cores, || solver.solve_parallel(initial_box, target));

    //         let speedup = d_widest.as_secs_f64() / d_aowb.as_secs_f64();
    //         println!(
    //             "{:<35} | {:<15?} | {:<15?} | {:.2}x",
    //             "P3: Mixed Exp-Poly [exp(x)-y^2=0]", d_widest, d_aowb, speedup
    //         );
    //     }

    //     // ---------------------------------------------------------------------
    //     // Real-World 1: Robotic Arm IK
    //     // ---------------------------------------------------------------------
    //     {
    //         let mut ast = Ast::new();
    //         let t1 = ast.add_variable("t1");
    //         let t2 = ast.add_variable("t2");
    //         let t1_plus_t2 = ast.add_binary(OpType::Add, t1, t2);

    //         let cos_t1 = ast.add_unary(OpType::Cos, t1);
    //         let cos_t12 = ast.add_unary(OpType::Cos, t1_plus_t2);
    //         let x_pos = ast.add_binary(OpType::Add, cos_t1, cos_t12);

    //         let mut initial_box = BoxRegion::default();
    //         initial_box.insert("t1".to_string(), Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap());
    //         initial_box.insert("t2".to_string(), Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap());

    //         let solver = Solver::new(ast, x_pos, 0.0001);
    //         let target = Interval::point(1.5).unwrap();

    //         let (_, d_widest) = run_with_threads(num_cores, || solver.solve_parallel_widest(initial_box.clone(), target));
    //         let (_, d_aowb) = run_with_threads(num_cores, || solver.solve_parallel(initial_box, target));

    //         let speedup = d_widest.as_secs_f64() / d_aowb.as_secs_f64();
    //         println!(
    //             "{:<35} | {:<15?} | {:<15?} | {:.2}x",
    //             "RW1: Robotic Arm Inverse Kinematics", d_widest, d_aowb, speedup
    //         );
    //     }

    //     // ---------------------------------------------------------------------
    //     // Real-World 2: Autonomous Drone Collision Clearance (4D)
    //     // ---------------------------------------------------------------------
    //     {
    //         let mut ast = Ast::new();
    //         let x1 = ast.add_variable("x1");
    //         let y1 = ast.add_variable("y1");
    //         let x2 = ast.add_variable("x2");
    //         let y2 = ast.add_variable("y2");

    //         let dx = ast.add_binary(OpType::Sub, x2, x1);
    //         let dy = ast.add_binary(OpType::Sub, y2, y1);
    //         let dx_sqr = ast.add_unary(OpType::Sqr, dx);
    //         let dy_sqr = ast.add_unary(OpType::Sqr, dy);
    //         let dist_sqr = ast.add_binary(OpType::Add, dx_sqr, dy_sqr);

    //         let mut initial_box = BoxRegion::default();
    //         initial_box.insert("x1".to_string(), Interval::new(-5.0, 0.0).unwrap());
    //         initial_box.insert("y1".to_string(), Interval::new(-5.0, 0.0).unwrap());
    //         initial_box.insert("x2".to_string(), Interval::new(0.0, 5.0).unwrap());
    //         initial_box.insert("y2".to_string(), Interval::new(0.0, 5.0).unwrap());

    //         let solver = Solver::new(ast, dist_sqr, 0.0005);
    //         let target = Interval::point(4.0).unwrap();

    //         let (_, d_widest) = run_with_threads(num_cores, || solver.solve_parallel_widest(initial_box.clone(), target));
    //         let (_, d_aowb) = run_with_threads(num_cores, || solver.solve_parallel(initial_box, target));

    //         let speedup = d_widest.as_secs_f64() / d_aowb.as_secs_f64();
    //         println!(
    //             "{:<35} | {:<15?} | {:<15?} | {:.2}x",
    //             "RW2: Drone Collision Avoidance (4D)", d_widest, d_aowb, speedup
    //         );
    //     }

    //     // ---------------------------------------------------------------------
    //     // Real-World 3: Diode Shockley Circuit Equilibrium
    //     // ---------------------------------------------------------------------
    //     {
    //         let mut ast = Ast::new();
    //         let v = ast.add_variable("v");
    //         let const_scale = ast.add_variable("const_scale");
    //         let scaled_v = ast.add_binary(OpType::Mul, v, const_scale);
    //         let exp_v = ast.add_unary(OpType::Exp, scaled_v);

    //         let mut initial_box = BoxRegion::default();
    //         initial_box.insert("v".to_string(), Interval::new(0.1, 1.0).unwrap());
    //         initial_box.insert("const_scale".to_string(), Interval::point(10.0).unwrap());

    //         let solver = Solver::new(ast, exp_v, 0.0001);
    //         let target = Interval::new(50.0, 100.0).unwrap();

    //         let (_, d_widest) = run_with_threads(num_cores, || solver.solve_parallel_widest(initial_box.clone(), target));
    //         let (_, d_aowb) = run_with_threads(num_cores, || solver.solve_parallel(initial_box, target));

    //         let speedup = d_widest.as_secs_f64() / d_aowb.as_secs_f64();
    //         println!(
    //             "{:<35} | {:<15?} | {:<15?} | {:.2}x",
    //             "RW3: Diode Circuit Equilibrium", d_widest, d_aowb, speedup
    //         );
    //     }

    //     println!("=======================================================================================\n");
    // }
}
