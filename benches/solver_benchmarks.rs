use criterion::{ Criterion, criterion_group, criterion_main };
use std::hint::black_box;
use ricp::ast::{ Ast, BoxRegion, OpType };
use ricp::interval::Interval;
use ricp::solver::Solver;
use std::time::Duration;

// -----------------------------------------------------------------------------
// P1: High-Degree Polynomial (x^4 + y^2 = 17)
// -----------------------------------------------------------------------------
fn bench_p1_high_degree_poly(c: &mut Criterion) {
    let mut ast = Ast::new();
    let x = ast.add_variable("x");
    let y = ast.add_variable("y");
    let x_sqr = ast.add_unary(OpType::Sqr, x);
    let x_4 = ast.add_unary(OpType::Sqr, x_sqr);
    let y_sqr = ast.add_unary(OpType::Sqr, y);
    let root = ast.add_binary(OpType::Add, x_4, y_sqr);

    let mut initial_box = BoxRegion::default();
    initial_box.insert("x".to_string(), Interval::new(-3.0, 3.0).unwrap());
    initial_box.insert("y".to_string(), Interval::new(-5.0, 5.0).unwrap());

    let solver = Solver::new_single(ast, root, Interval::point(17.0).unwrap(), 0.0001);
    // Group untuk membandingkan AOWB vs Widest secara langsung
    let mut group = c.benchmark_group("P1_High_Degree_Poly");
    group.measurement_time(Duration::from_secs(5)); // Duration test time
    group.sample_size(50);

    group.bench_function("AOWB", |b| {
        b.iter(|| solver.solve_parallel(black_box(initial_box.clone())))
    });

    group.bench_function("MaxWidth", |b| {
        b.iter(|| solver.solve_parallel_widest(black_box(initial_box.clone())))
    });

    group.finish();
}

// -----------------------------------------------------------------------------
// P2: Oscillatory Trigonometric (sin(x) * sin(y) = 0.5)
// -----------------------------------------------------------------------------
fn bench_p2_oscillatory_trig(c: &mut Criterion) {
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
    let mut group = c.benchmark_group("P2_Oscillatory_Trig");
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(50);

    group.bench_function("AOWB", |b| {
        b.iter(|| solver.solve_parallel(black_box(initial_box.clone())))
    });

    group.bench_function("MaxWidth", |b| {
        b.iter(|| solver.solve_parallel_widest(black_box(initial_box.clone())))
    });

    group.finish();
}

// -----------------------------------------------------------------------------
// P3: Mixed Exponential-Polynomial (exp(x) - y^2 = 0)
// -----------------------------------------------------------------------------
fn bench_p3_mixed_exp_poly(c: &mut Criterion) {
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
    let mut group = c.benchmark_group("P3_Mixed_Exp_Poly");
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(50);

    group.bench_function("AOWB", |b| {
        b.iter(|| solver.solve_parallel(black_box(initial_box.clone())))
    });

    group.bench_function("MaxWidth", |b| {
        b.iter(|| solver.solve_parallel_widest(black_box(initial_box.clone())))
    });

    group.finish();
}

// -----------------------------------------------------------------------------
// RW1: 2-DOF Robotic Arm Inverse Kinematics
// -----------------------------------------------------------------------------
fn bench_rw1_robotic_arm_ik(c: &mut Criterion) {
    let mut ast = Ast::new();
    let t1 = ast.add_variable("t1");
    let t2 = ast.add_variable("t2");
    let t1_plus_t2 = ast.add_binary(OpType::Add, t1, t2);

    let cos_t1 = ast.add_unary(OpType::Cos, t1);
    let cos_t12 = ast.add_unary(OpType::Cos, t1_plus_t2);
    let x_pos = ast.add_binary(OpType::Add, cos_t1, cos_t12);

    let mut initial_box = BoxRegion::default();
    initial_box.insert("t1".to_string(), Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap());
    initial_box.insert("t2".to_string(), Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap());

    let solver = Solver::new_single(ast, x_pos, Interval::point(1.5).unwrap(), 0.0001);
    let mut group = c.benchmark_group("RW1_Robotic_Arm_IK");
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(50);

    group.bench_function("AOWB", |b| {
        b.iter(|| solver.solve_parallel(black_box(initial_box.clone())))
    });

    group.bench_function("MaxWidth", |b| {
        b.iter(|| solver.solve_parallel_widest(black_box(initial_box.clone())))
    });

    group.finish();
}

// -----------------------------------------------------------------------------
// RW2: Drone Collision Zone (4D Spatial Clearance)
// -----------------------------------------------------------------------------
fn bench_rw2_drone_clearance(c: &mut Criterion) {
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

    let solver = Solver::new_single(ast, dist_sqr, Interval::point(4.0).unwrap(), 0.0005);
    let mut group = c.benchmark_group("RW2_Drone_Clearance_4D");
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(50);

    group.bench_function("AOWB", |b| {
        b.iter(|| solver.solve_parallel(black_box(initial_box.clone())))
    });

    group.bench_function("MaxWidth", |b| {
        b.iter(|| solver.solve_parallel_widest(black_box(initial_box.clone())))
    });

    group.finish();
}

// -----------------------------------------------------------------------------
// RW3: Diode Shockley Circuit Equilibrium
// -----------------------------------------------------------------------------
fn bench_rw3_diode_circuit_equilibrium(c: &mut Criterion) {
    let mut ast = Ast::new();
    let v = ast.add_variable("v");
    let const_scale = ast.add_variable("const_scale");
    let scaled_v = ast.add_binary(OpType::Mul, v, const_scale);
    let exp_v = ast.add_unary(OpType::Exp, scaled_v);

    let mut initial_box = BoxRegion::default();
    initial_box.insert("v".to_string(), Interval::new(0.1, 1.0).unwrap());
    initial_box.insert("const_scale".to_string(), Interval::point(10.0).unwrap());

    let solver = Solver::new_single(ast, exp_v, Interval::new(50.0, 100.0).unwrap(), 0.0001);
    let mut group = c.benchmark_group("RW3_Diode_Equilibrium");
    group.measurement_time(Duration::from_secs(5));
    group.sample_size(50);

    group.bench_function("AOWB", |b| {
        b.iter(|| solver.solve_parallel(black_box(initial_box.clone())))
    });

    group.bench_function("MaxWidth", |b| {
        b.iter(|| solver.solve_parallel_widest(black_box(initial_box.clone())))
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_p1_high_degree_poly,
    bench_p2_oscillatory_trig,
    bench_p3_mixed_exp_poly,
    bench_rw1_robotic_arm_ik,
    bench_rw2_drone_clearance,
    bench_rw3_diode_circuit_equilibrium
);
criterion_main!(benches);
