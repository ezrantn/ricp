# 🦀 ricp

> [!WARNING]
> This project is a work in progress and may contain bugs or incomplete features.

**A Sound, High-Performance, and Multi-Threaded Non-Linear Automated Reasoning Engine written in Pure Rust.**

## Overview

**`ricp`** (*Rust Interval Constraint Propagation*) is a lightweight, zero-dependency, sound SMT/Automated Reasoning Proof-of-Concept engine for $\delta$-satisfiability over Non-Linear Real Arithmetic ($\text{NRA}$).

Inspired by tools like **dReal** and **Z3**, `ricp` addresses two major pain points in traditional C++ SMT solvers: **floating-point unsoundness** and **thread synchronization overhead during search space branching**. By leveraging Rust's strict memory safety model and Rayon's lock-free work-stealing scheduler, `ricp` delivers sound bounds with deterministic multi-core speedups.
