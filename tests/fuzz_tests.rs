mod common;

use crate::common::fuzzer::SmtFuzzer;
use ::rand::rngs::ThreadRng;
use semitone::parser::SmtParser;
use std::fs;
use std::io::Write;
use std::process::{Command, Stdio};
use tracing::info;

fn run_z3_oracle(script: &str) -> String {
    let mut child = Command::new("z3").args(&["-in", "-T:10"]).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().expect("Failed to spawn Z3 process");
    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(script.as_bytes()).expect("Failed to write to Z3 stdin");
    }
    let output = child.wait_with_output().expect("Failed to read Z3 output");
    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

fn run_semitone(script: &str) -> String {
    let mut output = Vec::new();
    let mut runner = SmtParser::new(&mut output);
    runner.run_str(script);
    String::from_utf8_lossy(&output).trim().to_string()
}

#[test]
fn test_no_crashes_on_random_inputs() {
    let mut rng = ThreadRng::default();
    let mut fuzzer = SmtFuzzer::new();

    for _ in 0..1000 {
        let script = fuzzer.generate_script(&mut rng, 20);
        info!("Fuzzing with script:\n{}", script);

        let mut sink = std::io::sink();
        let mut runner = SmtParser::new(&mut sink);

        runner.run_str(&script);
    }
}

#[test]
fn test_differential_fuzzing_with_z3() {
    let mut rng = ThreadRng::default();
    let mut fuzzer = SmtFuzzer::new();

    for i in 1..=1000 {
        let script = fuzzer.generate_script(&mut rng, 15);
        fs::write("last_fuzz.smt2", &script).expect("Failed to write last_fuzz.smt2");
        let z3_result = run_z3_oracle(&script);

        if z3_result != "sat" && z3_result != "unsat" {
            continue;
        }

        let semitone_result = run_semitone(&script).trim().to_string();

        if semitone_result != z3_result {
            let crash_file = format!("crash_{}.smt2", i);
            fs::write(&crash_file, &script).unwrap();
            panic!("Differential fuzzing failed on script:\n{}\nZ3 result: {}\nSeMiTONE result: {}\nSaved to {}", script, z3_result, semitone_result, crash_file);
        }
    }
}
