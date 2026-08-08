# SeMiTONE

[![Crate](https://img.shields.io/crates/v/semitone?logo=rust)](https://crates.io/crates/semitone)
[![Docs](https://docs.rs/semitone/badge.svg)](https://docs.rs/semitone)
[![Rust](https://img.shields.io/badge/Rust-1.95+-orange?logo=rust)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/License-MIT-green)](LICENSE)
![Build Status](https://github.com/pstlab/SeMiTONE/actions/workflows/rust.yml/badge.svg)
[![codecov](https://codecov.io/gh/pstlab/SeMiTONE/branch/main/graph/badge.svg)](https://codecov.io/gh/pstlab/SeMiTONE)

**SeMiTONE** (Satisfiability Modulo TheOries NEtwork) is a highly modular, Rust-native foundation for building custom Satisfiability Modulo Theories (SMT) and Optimization Modulo Theories (OMT) solvers.

While most SMT projects provide monolithic, black-box solvers, SeMiTONE takes a different approach. It provides the **core mathematical engine and backtrackable data structures** required to evaluate formulas against background theories, deliberately delegating the "search" phase (e.g., DPLL/CDCL branching loops and resolution heuristics) to external modules. 

This makes SeMiTONE the perfect building block for researchers and engineers who need deep integration of logic reasoning into their own architectures without being constrained by a rigid, pre-packaged solver.

## 🚀 Key Features

* **Lazy Lemmatization Framework:** Seamlessly delegates theory evaluation to specialized underlying modules, enabling an efficient DPLL(T) architecture.
* **Advanced Theory Support:** 
  * **Linear Real Arithmetic (LRA):** Fast simplex-based evaluation with native support for infinitesimals, strict/non-strict bounds, Gomory fractional cuts, and Branch & Bound for integer variables.
  * **Enumerative Domains (Enum):** Arc-consistency propagation for finite domains.
* **CDCL-Ready:** Automatically performs conflict analysis, generates precise *no-goods* (theory lemmas), and computes optimal backjump levels (e.g., 1UIP) to aggressively prune the search space.
* **Fully Incremental:** Features zero-cost context switching (`push`/`pop`) and solving under assumptions, ideal for iterative constraint refinement.
* **Rust-Native Performance:** Zero-allocation pivoting, sparse matrix representations, and robust memory management.

## 🎯 Ideal Use Cases

SeMiTONE is designed for domains that require tightly coupled, custom logic reasoning, such as:
* **Timeline-based Automated Planning:** Formulating and solving complex temporal networks and resource constraints.
* **Cognitive Architectures:** Integrating semantic reasoning and dynamic constraint satisfaction into intelligent agents.
* **Custom SMT/OMT Solvers:** Building specialized solvers tailored to niche theories or domain-specific heuristics.

## 🛠️ Quick Look

SeMiTONE exposes a clean, strongly-typed AST to build and assert constraints. Below is a conceptual example of how constraints are loaded and propagated:

```rust
use semitone::smt::{SmtSolver, ast::*};

let mut solver = SmtSolver::new();

// Declare variables across different theories
let x = solver.new_real();
let y = solver.new_real();
let state = solver.new_enum(vec![1, 2, 3]);

// Build constraints: (x + y = 10) AND (x > 6)
let eq_expr = eq_arith(add([x.clone(), y.clone()]), cst_arith(10));
let gt_expr = gt(x, cst_arith(6));

// Assert constraints to the network
let system = and([eq_expr, gt_expr]);
match solver.assert(&system) {
    Ok(_) => println!("Constraints are feasible. Ready for search!"),
    Err((level, conflict_lemma)) => println!("Conflict detected at level {}!", level),
}
```

*Note: As SeMiTONE delegates search to external modules, you will need to wrap the network in your own decision loop to explore the boolean space and extract a final model.*

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.