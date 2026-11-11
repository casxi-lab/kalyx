//! Repository tasks for kalyx, run from the repository root as
//! `cargo xtask <command>`.

mod check;
mod commits;
mod docs;
mod formal;
mod guard;
mod receipt;
mod repo;
mod scan;
#[cfg(test)]
mod scratch;
mod subset;
mod workflows;

use std::path::PathBuf;
use std::process::ExitCode;

/// A command of `cargo xtask`, possibly with subcommands of its own.
pub struct Command {
    pub name: &'static str,
    pub about: &'static str,
    pub subcommands: &'static [Command],
}

/// Every command that `cargo xtask` provides, with what it does.
pub const COMMANDS: &[Command] = &[
    Command {
        name: "check",
        about: "Run the format, Clippy and test checks of xtask, the documentation, commit message and workflow checks, the format, Clippy and test checks of the kalyx package, its allocation check, the Lean source and provable-subset checks and its guard; with --receipt <path>, also write a JSON receipt of the run",
        subcommands: &[],
    },
    Command {
        name: "formal",
        about: "The proof tooling; without a subcommand, list its commands",
        subcommands: formal::COMMANDS,
    },
    Command {
        name: "help",
        about: "List the commands",
        subcommands: &[],
    },
];

fn print_help() {
    println!("Usage: cargo xtask <command>\n\nCommands:");
    for command in COMMANDS {
        println!("  {:<8} {}", command.name, command.about);
        for subcommand in command.subcommands {
            println!(
                "  {:<8} {:<16} {}",
                command.name, subcommand.name, subcommand.about
            );
        }
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
        ["formal", rest @ ..] => formal::run(&repo::root(), rest),
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
