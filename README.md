# 🦀 ricp — Rust Interval Constraint Propagation

<div align="center">

[![Rust](https://img.shields.io/badge/rust-1.75%2B-orange.svg?style=flat-square&logo=rust)](https://www.rust-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg?style=flat-square)](LICENSE)
[![Build Status](https://img.shields.io/badge/tests-passing-brightgreen.svg?style=flat-square)](#)
[![arXiv](https://img.shields.io/badge/arXiv-Preprint-B31B1B.svg?style=flat-square&logo=arxiv)](#)

**A Sound, High-Performance, and Multi-Threaded Non-Linear Automated Reasoning Engine written in Pure Rust.**

[Key Features](#-key-features) •
[Architecture](#-architecture) •
[Quickstart](#-quickstart) •
[Benchmark](#-benchmarks) •
[License](#-license)

</div>

---

## Overview

**`ricp`** (*Rust Interval Constraint Propagation*) is a lightweight, zero-dependency, sound SMT/Automated Reasoning Proof-of-Concept engine for $\delta$-satisfiability over Non-Linear Real Arithmetic ($\text{NRA}$).

Inspired by tools like **dReal** and **Z3**, `ricp` addresses two major pain points in traditional C++ SMT solvers: **floating-point unsoundness** and **thread synchronization overhead during search space branching**. By leveraging Rust's strict memory safety model and Rayon's lock-free work-stealing scheduler, `ricp` delivers sound bounds with deterministic multi-core speedups.

---

## Key Features

* **IEEE-754 Sound Interval Arithmetic:** Employs directed rounding (`next_down` / `next_up`) to guarantee over-approximation, eliminating floating-point rounding errors.
* **Borrow-Checker Friendly AST:** Index-based arena allocation (`Vec<Node>` + `usize`) for dual-pass (Forward/Backward) traversal without reference aliasing overhead.
* **HC4 Contractor Engine:** Efficient Hull Consistency (HC4) implementation for fast interval squeezing on continuous constraints.
* **Fearless Parallelism:** Lock-free, work-stealing Branch-and-Prune loop powered by `rayon`, enabling scalable parallel $\delta$-SAT search across all CPU cores.
* **Transcendental Support:** Built-in interval arithmetic for non-linear transcendental functions ($\sin, \cos, \exp, \sqrt{x}$).

---

## Quickstart

### Prerequisites

* [Rust 1.75+](https://www.rust-lang.org/tools/install)

### Installation

Add `ricp` to your `Cargo.toml`:

```toml
[dependencies]
ricp = { git = "[https://github.com/ezrantn/ricp](https://github.com/ezrantn/ricp)" }
rayon = "1.10"
```

Usage Example: Solving Transcendental SystemHere is how to solve the non-linear equation $\sin(x) + e^y = 2.0$ over $x \in [0, \frac{\pi}{2}]$ and $y \in [-2, 2]$ with precision $\delta = 0.001$:

```rust
use ricp::ast::{Ast, BoxRegion, OpType};
use ricp::interval::Interval;
use ricp::solver::{Solver, SolverResult};

fn main() {
    // 1. Construct AST: sin(x) + exp(y) = 2.0
    let mut ast = Ast::new();
    let x = ast.add_variable("x");
    let y = ast.add_variable("y");
    
    let sin_x = ast.add_unary(OpType::Sin, x);
    let exp_y = ast.add_unary(OpType::Exp, y);
    let root = ast.add_binary(OpType::Add, sin_x, exp_y);

    // 2. Define Initial Search Domain (BoxRegion)
    let mut initial_box = BoxRegion::new();
    initial_box.insert("x".to_string(), Interval::new(0.0, std::f64::consts::FRAC_PI_2).unwrap());
    initial_box.insert("y".to_string(), Interval::new(-2.0, 2.0).unwrap());

    // 3. Initialize Parallel Solver (delta precision = 0.001)
    let solver = Solver::new(ast, root, 0.001);
    let target = Interval::point(2.0).unwrap();

    // 4. Solve in Parallel
    match solver.solve_parallel(initial_box, target) {
        SolverResult::Sat(sat_box) => {
            let x_res = sat_box.get("x").unwrap();
            let y_res = sat_box.get("y").unwrap();

            println!("SAT Solution Found!");
            println!("x ∈ [{:.5}, {:.5}]", x_res.low, x_res.high);
            println!("y ∈ [{:.5}, {:.5}]", y_res.low, y_res.high);
        }
        SolverResult::Unsat => println!("UNSAT: Domain proved to contain no solution."),
    }
}
```
---

## Benchmarks

Benchmark executed on the non-linear circle benchmark ($x^2 + y^2 = 25$) with a wide search domain $x, y \in [-10, 10]$ and tight precision $\delta = 0.0001$:

Execution Strategy,CPU Cores / Threads,Execution Time,Speedup Factor
Single-Threaded,1 Thread,1.695 s,1.00x
Multi-Threaded (ricp),All Cores (Rayon),0.372 s,🔥 4.56x

Run the benchmarks locally using:

```bash
cargo test test_benchmark_rayon_speedup -- --nocapture
```

---

## Roadmap

- [x] Phase 1: IEEE-754 Sound Directed Rounding Interval Arithmetic
- [x] Phase 2: Index-based AST Arena & HC4 Contractor (Forward/Backward)
- [x] Phase 3: Parallel Work-Stealing Branch-and-Prune Search Engine
- [x] Phase 4: Non-Linear Transcendental Support ($\sin, \cos, \exp$)
- [ ] Phase 5: SMT-LIB2 Parser Integration & CDCL(T) Coupling

---

## License

Distributed under the MIT License. See LICENSE for more information.