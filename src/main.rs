use std::env;
use std::io::{self, Read};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: semitone <file.smt2 | ->");
        std::process::exit(1);
    }

    let file_path = &args[1];
    let mut stdout = std::io::stdout();
    let mut runner = semitone::parser::SmtParser::new(&mut stdout);

    if file_path == "-" {
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer).expect("Failed to read from stdin");
        runner.run_str(&buffer);
    } else {
        // Altrimenti, apri normalmente il file
        runner.run_file(file_path);
    }
}
