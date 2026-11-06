//! Repository tasks for kalyx, run from the repository root as
//! `cargo xtask <command>`.

mod check;
mod commits;
mod docs;
mod receipt;
mod repo;
mod workflows;

use std::path::PathBuf;
use std::process::ExitCode;

/// Every command that `cargo xtask` provides, with what it does.
const COMMANDS: &[(&str, &str)] = &[
    (
        "check",
        "Run the format, Clippy, test, documentation, commit message and workflow checks; with --receipt <path>, also write a JSON receipt of the run",
    ),
    ("help", "List the commands"),
];

fn print_help() {
    println!("Usage: cargo xtask <command>\n\nCommands:");
    for (name, about) in COMMANDS {
        println!("  {name:<8} {about}");
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .as_slice()
    {
        ["check"] => check::run(repo::root(), None),
        ["check", "--receipt", path] => check::run(repo::root(), Some(PathBuf::from(path))),
        [] | ["help"] => {
            print_help();
            ExitCode::SUCCESS
        }
        _ => {
            eprintln!("unknown command: cargo xtask {}\n", args.join(" "));
            print_help();
            ExitCode::from(2)
        }
    }
}
