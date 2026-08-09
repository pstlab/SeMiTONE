use criterion::{Criterion, criterion_group, criterion_main};
use semitone::parser::SmtParser;
use std::hint::black_box;

fn bench_smt_parser_simple_lra(c: &mut Criterion) {
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
            let mut sink = std::io::sink();
            let mut runner = SmtParser::new(&mut sink);

            // black_box prevents the compiler from optimizing away the string
            runner.run_str(black_box(script));
        })
    });
}

fn bench_smt_parser_logistics(c: &mut Criterion) {
    // A complex stress-test involving Tseitin encoding, multiple contexts (push/pop),
    // boolean/arithmetic integration, and forced backjumping.
    let script = r#"
        (set-logic QF_LRA)
        (declare-fun q1 () Real)
        (declare-fun q2 () Real)
        (declare-fun q3 () Real)
        (declare-fun q4 () Real)
        (declare-fun on1 () Bool)
        (declare-fun on2 () Bool)
        (declare-fun on3 () Bool)
        (declare-fun on4 () Bool)
        
        (assert (>= q1 0.0))
        (assert (>= q2 0.0))
        (assert (>= q3 0.0))
        (assert (>= q4 0.0))
        
        (assert (=> on1 (<= q1 300.0)))
        (assert (=> (not on1) (= q1 0.0)))
        (assert (=> on2 (<= q2 400.0)))
        (assert (=> (not on2) (= q2 0.0)))
        (assert (=> on3 (<= q3 500.0)))
        (assert (=> (not on3) (= q3 0.0)))
        (assert (=> on4 (<= q4 200.0)))
        (assert (=> (not on4) (= q4 0.0)))
        
        (assert (not (and on3 on4)))
        (assert (=> on1 on2))
        
        (push 1)
        (assert (= (+ q1 q2 q3 q4) 750.0))
        (assert (<= q2 150.0))
        (check-sat)
        (pop 1)
        
        (push 1)
        (assert (= (+ q1 q2 q3 q4) 1000.0))
        (assert (not on3))
        (check-sat)
        (pop 1)
    "#;

    c.bench_function("parse_and_solve_logistics", |b| {
        b.iter(|| {
            let mut sink = std::io::sink();
            let mut runner = SmtParser::new(&mut sink);
            runner.run_str(black_box(script));
        })
    });
}

// Boilerplate to configure and run Criterion
criterion_group!(benches, bench_smt_parser_simple_lra, bench_smt_parser_logistics);
criterion_main!(benches);
