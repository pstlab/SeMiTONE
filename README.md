# SeMiTONE

[![Crate](https://img.shields.io/crates/v/semitone?logo=rust)](https://crates.io/crates/semitone)
[![Docs](https://docs.rs/semitone/badge.svg)](https://docs.rs/semitone)
[![Rust](https://img.shields.io/badge/Rust-1.95+-orange?logo=rust)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/License-MIT-green)](LICENSE)
![Build Status](https://github.com/pstlab/SeMiTONE/actions/workflows/rust.yml/badge.svg)
[![codecov](https://codecov.io/gh/pstlab/SeMiTONE/branch/main/graph/badge.svg)](https://codecov.io/gh/pstlab/SeMiTONE)

Satisfiability Modulo Theories (SMT) concerns the satisfiability of formulas with respect to some background theory. SeMiTONE is a Satisfiability Modulo TheOries NEtwork, allowing the creation of variables and constraints in different underlying theories.

SeMiTONE maintains backtrackable data structures, allows the creation of variables and constraints, performs constraint propagation and, whenever conflicts arise, performs conflict analysis, learns a no-good and backjumps to the highest level. It is worth noting that SeMiTONE is not an SMT solver. SeMiTONE is, on the contrary, a network on top of which SMT solvers can be built. In this regard, SeMiTONE deliberately neglects all the aspects related to 'search' as, for example, search algorithms and resolution heuristics, demanding to external modules solving SMT problems.