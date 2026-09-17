use semitone::parser::SmtParser;
use std::env;
use std::io::{self, Read};
use tracing::{Level, error, subscriber};

fn main() {
    let subscriber = tracing_subscriber::fmt().with_max_level(Level::WARN).finish();
    subscriber::set_global_default(subscriber).expect("Failed to set global default subscriber");

    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        error!("Usage: semitone <file.smt2 | ->");
        std::process::exit(1);
    }

    let file_path = &args[1];
    let mut stdout = std::io::stdout();
    let mut runner = SmtParser::new(&mut stdout);

    if file_path == "-" {
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer).expect("Failed to read from stdin");
        runner.run_str(&buffer);
    } else {
        // Otherwise, open the file normally
        runner.run_file(file_path);
    }
}
