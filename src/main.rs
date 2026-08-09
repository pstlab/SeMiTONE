use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: semitone <file.smt2>");
        return;
    }

    let mut stdout = std::io::stdout();
    let mut runner = semitone::parser::SmtParser::new(&mut stdout);
    runner.run_file(&args[1]);
}
