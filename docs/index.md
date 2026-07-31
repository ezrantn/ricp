# ricp

**A Ridiculously Fast, Sound & Lock-Free Non-linear Real Arithmetic (NRA) Theory Engine in Pure Rust.**

---

## What is `ricp`?

**`ricp`** (*Rust Interval Constraint Propagation*) is a mathematical continuous theory engine / solver designed to find precise solutions for complex non-linear continuous constraint systems over real numbers.

In short, `ricp` receives mathematical constraints (including trigonometric, exponential, and high-degree polynomial functions) and automatically contracts search spaces (*interval regions*) to isolate valid variable bounds.

---

## Background Problem

Solving non-linear continuous constraints—particularly within the domain of **Non-linear Real Arithmetic (NRA)**—is one of the most computationally demanding tasks in mathematical reasoning and Formal Verification / SMT Solving.

1. **Curse of Dimensionality:** Recursively bisecting continuous variable search spaces generates sub-boxes at an exponential rate ($2^N$).
2. **Floating-Point Inaccuracy:** Standard computer arithmetic introduces rounding errors, which can compromise safety-critical systems like robotics and autonomous drone navigation.
3. **Real-Time Latency Limitations:** Traditional NRA solvers often take seconds or minutes, making them unsuitable for control loops requiring millisecond-level responsiveness.

---

## Purpose & Goals

`ricp` was engineered to address these challenges with three core objectives:

* **Deliver Real-Time Solving Speeds:** Reduce continuous search times down to millisecond and sub-millisecond bounds, enabling direct integration into robotic control loops, circuit simulations, and collision avoidance systems.
* **Guarantee Mathematical Soundness:** Prevent *False SAT* (false positive solutions) by leveraging IEEE-754 hardware-based directed rounding.
* **Maximize Modern Hardware Throughput:** Exploit lock-free parallel execution built on Rust's static concurrency model to achieve optimal multi-core scaling.

---

## Key Features

<div class="grid cards" markdown>

-   **Real-Time Performance**
    ---
    Solves complex transcendental, trigonometric, and exponential constraints in **milliseconds to sub-milliseconds** ($874.9\,\mu\text{s}$).

-   **Mathematically Sound**
    ---
    Guarantees zero false positives via IEEE-754 hardware directed rounding (`next_down`/`next_up`) without external C dependencies.

-   **Lock-Free Parallel Scaling**
    ---
    Leverages Rust's static thread-safety guarantees (`Send`/`Sync`) for efficient multi-core scaling without mutex lock contention.

-   **Zero-Allocation Hot Loops**
    ---
    Uses a ultra-lightweight internal data layout for maximum cache locality and peak memory efficiency.

</div>

---

## Quick Benchmarks

Measured under isolated release execution (`cargo test benchmark --release -- --test-threads=1 --nocapture`):

| Benchmark Scenario | Constraint Domain | 1-Thread | 16-Threads | Speedup |
| :--- | :--- | :---: | :---: | :---: |
| **RW3: Semiconductor Equilibrium** | Non-Linear Exponential ($\exp(10v)$) | $1.84\,\text{ms}$ | **$874.9\,\mu\text{s}$** | $2.10\times$ |
| **P3: Mixed Exp-Poly** | $\exp(x) - y^2 = 0$ | $12.01\,\text{ms}$ | **$2.12\,\text{ms}$** | **$5.67\times$** |
| **RW1: 2-DOF Robotic Arm IK** | $\cos(t_1) + \cos(t_1+t_2) = 1.5$ | $20.73\,\text{ms}$ | **$4.69\,\text{ms}$** | $4.42\times$ |
| **RW2: Drone Collision (4D)** | Euclidean Safety Clearance Boundary | $209.67\,\text{ms}$ | **$41.13\,\text{ms}$** | $5.10\times$ |

---

## Warning

ricp is currently an active work-in-progress. While we are engineering ricp to meet the standards of production-grade SMT solvers through rigorous real-world testing, some core components are still under construction.

Currently, the core Non-linear Real Arithmetic (NRA) engine is fully operational. Front-end input parsers and the CDCL(T) framework are actively in development.