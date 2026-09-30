# SeMiTONE

[![Crate](https://img.shields.io/crates/v/semitone?logo=rust)](https://crates.io/crates/semitone)
[![Docs](https://docs.rs/semitone/badge.svg)](https://docs.rs/semitone)
[![Rust](https://img.shields.io/badge/Rust-1.95+-orange?logo=rust)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/License-MIT-green)](https://github.com/pstlab/SeMiTONE/blob/HEAD/LICENSE)
![Build Status](https://github.com/pstlab/SeMiTONE/actions/workflows/rust.yml/badge.svg)
[![codecov](https://codecov.io/gh/pstlab/SeMiTONE/branch/main/graph/badge.svg)](https://codecov.io/gh/pstlab/SeMiTONE)

**SeMiTONE** (Satisfiability Modulo TheOries NEtwork) is a modular Rust library for building SMT solvers and integrating theory reasoning into custom search procedures. Its public API exposes typed expressions, theory propagation, decision levels, clauses, and backtracking. An optional built-in DPLL(T) search loop and an SMT-LIB interface are available through Cargo features.

## 🚀 Key Features

* **Theory reasoning:** Linear real and integer arithmetic, difference logic, finite-domain enums, and equality with uninterpreted functions.
* **Incremental scopes:** `push` and `pop` save and restore SAT and theory state.
* **Search integration:** Propagation reports conflict clauses and suggested backtrack levels; applications can provide their own search loop or enable the built-in `solver` feature.
* **SMT-LIB support:** The optional `parser` feature provides the SMT-LIB interface and enables the built-in solver.
* **Sparse arithmetic:** The LRA engine uses an incremental simplex tableau and exact rational arithmetic, including infinitesimals for strict bounds and branch-and-bound/Gomory cuts for integer variables.

## 🎯 Ideal Use Cases

SeMiTONE is designed for domains that require tightly coupled, custom logic reasoning, such as:
* **Timeline-based Automated Planning:** Formulating and solving complex temporal networks and resource constraints.
* **Cognitive Architectures:** Integrating semantic reasoning and dynamic constraint satisfaction into intelligent agents.
* **Custom SMT/OMT Solvers:** Building specialized solvers tailored to niche theories or domain-specific heuristics.

## 🛠️ Quick Look

`assert` adds a constraint to the current context and can report an immediate conflict. It does not by itself check full theory feasibility. Call `propagate` to process queued SAT assignments and detect theory conflicts. Both methods return `Ok(())` on success or `Err((backtrack_level, clause))` on conflict; the clause is an explanation suitable for learning, and the level is the suggested non-chronological backtrack target.

```rust
use semitone::SeMiTONE;

let mut solver = SeMiTONE::new();

let x = solver.new_real();
let y = solver.new_real();
let state = solver.new_enum([1, 2, 3]);

let constraints = (&x + &y).eq(10) & x.gt(6);
if let Err((level, clause)) = solver.assert(constraints) {
    println!("Conflict at backtrack level {level}: {clause:?}");
    return;
}

match solver.propagate() {
    Ok(()) => {
        if solver.decide_enum(&state, 2) {
            match solver.propagate() {
                Ok(()) => println!("The current branch has no detected conflict."),
                Err((level, clause)) => {
                    println!("Conflict at backtrack level {level}: {clause:?}");
                }
            }
        } else {
            println!("The enum decision conflicts with the current assignment.");
        }
    }
    Err((level, clause)) => {
        println!("Conflict at backtrack level {level}: {clause:?}");
    }
}
```

For complete SAT/SMT search and model construction, use the optional `solver` feature or build a search loop around `decide`, `propagate`, `cancel_until`, and `check_ints`. A successful `propagate` only means no conflict was found by the propagation procedures; it is not by itself a complete SAT result.

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](https://github.com/pstlab/SeMiTONE/blob/HEAD/LICENSE) file for details.