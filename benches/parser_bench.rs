use criterion::{Criterion, criterion_group, criterion_main};
use semitone::parser::SmtParser;
use std::hint::black_box;

fn bench_smt_parser(c: &mut Criterion) {
    // A standard QF_LRA problem: intersection of lines and bounds
    let script = r#"
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (>= x 0.0))
        (assert (>= y 0.0))
        (assert (<= (+ (* 2.0 x) y) 10.0))
        (assert (<= (+ x (* 2.0 y)) 10.0))
        (check-sat)
    "#;

    c.bench_function("parse_and_solve_lra", |b| {
        b.iter(|| {
            // We instantiate a new parser inside the loop to ensure
            // a completely fresh SMT state for every iteration.
            let mut runner = SmtParser::new();

            // black_box prevents the compiler from optimizing away the string
            runner.run_str(black_box(script));
        })
    });
}

// Boilerplate to configure and run Criterion
criterion_group!(benches, bench_smt_parser);
criterion_main!(benches);
