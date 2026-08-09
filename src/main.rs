use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: semitone <file.smt2>");
        return;
    }

    let mut runner = semitone::parser::SmtParser::new();
    runner.run_file(&args[1]);
}
