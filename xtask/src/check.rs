//! `cargo xtask check`: the repository checks, in order, stopping at the
//! first failure.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{Duration, Instant};

use crate::repo::{Entry, Tree};
use crate::{commits, docs, guard, receipt, workflows};

/// The manifest of the xtask workspace, which the `fmt`, `clippy` and `test`
/// steps cover, relative to the repository root.
pub const MANIFEST: &str = "xtask/Cargo.toml";

/// The manifest of the kalyx package at the repository root, which the
/// `kalyx-fmt`, `kalyx-clippy` and `kalyx-test` steps cover.
pub const PACKAGE_MANIFEST: &str = "Cargo.toml";

/// The manifest of the allocation check, a workspace of its own outside the
/// package, which the `kalyx-allocation` step covers and runs.
pub const ALLOCATION_MANIFEST: &str = "checks/allocation/Cargo.toml";

/// A command run in the repository root.
#[derive(Debug, Clone)]
pub struct Cmd {
    pub program: OsString,
    pub args: Vec<String>,
}

/// Named values that a step observed, in the order it observed them, for the
/// receipt. A step adds them as it goes, so they are kept when it fails.
pub type Facts = Vec<(String, String)>;

/// A check written in this crate, run with the repository root.
pub type Check = Box<dyn Fn(&Path, &mut Facts) -> Result<(), String>>;

/// What a step does.
pub enum Action {
    /// Run commands in order; each must exit with status 0.
    Commands(Vec<Cmd>),
    /// Run a check written in this crate.
    Internal(Check),
}

/// A named step of the check.
pub struct Step {
    pub name: &'static str,
    pub action: Action,
}

/// How a step ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Status {
    /// The step passed.
    Passed,
    /// The step failed, and why.
    Failed(String),
    /// An earlier step failed, so this one did not run.
    NotRun,
}

/// The result of one step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Outcome {
    pub step: &'static str,
    pub status: Status,
    pub duration: Duration,
    pub facts: Facts,
}

/// A Cargo command on the package or workspace of `manifest`: `args`, the
/// manifest, then `trailing`.
fn cargo(manifest: &str, args: &[&str], trailing: &[&str]) -> Cmd {
    let mut all: Vec<String> = args.iter().map(|arg| arg.to_string()).collect();
    all.push("--manifest-path".into());
    all.push(manifest.into());
    all.extend(trailing.iter().map(|arg| arg.to_string()));
    Cmd {
        program: std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()),
        args: all,
    }
}

/// The steps of `cargo xtask check`, in the order they run.
pub fn steps() -> Vec<Step> {
    vec![
        Step {
            name: "fmt",
            action: Action::Commands(vec![cargo(MANIFEST, &["fmt", "--all", "--check"], &[])]),
        },
        Step {
            name: "clippy",
            action: Action::Commands(vec![cargo(
                MANIFEST,
                &["clippy", "--workspace", "--all-targets", "--locked"],
                &["--", "-D", "warnings"],
            )]),
        },
        Step {
            name: "test",
            action: Action::Commands(vec![cargo(
                MANIFEST,
                &["test", "--workspace", "--locked"],
                &[],
            )]),
        },
        Step {
            name: "docs",
            action: Action::Internal(Box::new(|root, _| docs::run(root))),
        },
        Step {
            name: "commits",
            action: Action::Internal(Box::new(commits::run)),
        },
        Step {
            name: "workflows",
            action: Action::Internal(Box::new(check_workflows)),
        },
        Step {
            name: "kalyx-fmt",
            action: Action::Commands(vec![cargo(
                PACKAGE_MANIFEST,
                &["fmt", "--all", "--check"],
                &[],
            )]),
        },
        Step {
            name: "kalyx-clippy",
            action: Action::Commands(vec![cargo(
                PACKAGE_MANIFEST,
                &["clippy", "--all-targets", "--locked"],
                &["--", "-D", "warnings"],
            )]),
        },
        Step {
            name: "kalyx-test",
            action: Action::Commands(vec![cargo(PACKAGE_MANIFEST, &["test", "--locked"], &[])]),
        },
        Step {
            name: "kalyx-allocation",
            action: Action::Commands(vec![
                cargo(ALLOCATION_MANIFEST, &["fmt", "--all", "--check"], &[]),
                cargo(
                    ALLOCATION_MANIFEST,
                    &["clippy", "--all-targets", "--locked"],
                    &["--", "-D", "warnings"],
                ),
                cargo(ALLOCATION_MANIFEST, &["test", "--locked"], &[]),
                cargo(ALLOCATION_MANIFEST, &["run", "--locked"], &[]),
            ]),
        },
        Step {
            name: "guard",
            action: Action::Internal(Box::new(guard::run)),
        },
    ]
}

/// The workflows step on the tracked files; the files it read become facts.
fn check_workflows(root: &Path, facts: &mut Facts) -> Result<(), String> {
    let tree = Tree::load(root)?;
    let tracked = || {
        tree.entries().map(|(path, entry)| match entry {
            Entry::File(bytes) => (path, Some(bytes.as_slice())),
            Entry::Symlink | Entry::Submodule => (path, None),
        })
    };
    let files: Vec<&str> = tracked()
        .map(|(path, _)| path)
        .filter(|path| workflows::is_workflow(path))
        .collect();
    if files.is_empty() {
        println!("workflows: no workflow files");
    } else {
        println!("workflows: {}", files.join(", "));
    }
    facts.push(("files".to_string(), files.join(", ")));
    let problems = workflows::check(tracked());
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// Runs `steps` in order in `root` and stops at the first failure. Every
/// step has an outcome; those after a failure did not run.
pub fn run_steps(root: &Path, steps: &[Step]) -> Vec<Outcome> {
    let mut outcomes = Vec::new();
    let mut failed = false;
    for step in steps {
        let mut facts = Facts::new();
        if failed {
            outcomes.push(Outcome {
                step: step.name,
                status: Status::NotRun,
                duration: Duration::ZERO,
                facts,
            });
            continue;
        }
        println!("==> {}", step.name);
        let started = Instant::now();
        let result = match &step.action {
            Action::Commands(commands) => {
                commands.iter().try_for_each(|cmd| run_command(root, cmd))
            }
            Action::Internal(check) => check(root, &mut facts),
        };
        let status = match result {
            Ok(()) => Status::Passed,
            Err(detail) => {
                failed = true;
                Status::Failed(detail)
            }
        };
        outcomes.push(Outcome {
            step: step.name,
            status,
            duration: started.elapsed(),
            facts,
        });
    }
    outcomes
}

/// The failed step and why it failed, if one did.
pub fn failure(outcomes: &[Outcome]) -> Option<(&'static str, &str)> {
    outcomes.iter().find_map(|outcome| match &outcome.status {
        Status::Failed(detail) => Some((outcome.step, detail.as_str())),
        _ => None,
    })
}

fn run_command(root: &Path, cmd: &Cmd) -> Result<(), String> {
    let shown = format!("{} {}", cmd.program.to_string_lossy(), cmd.args.join(" "));
    println!("$ {shown}");
    let status = Command::new(&cmd.program)
        .args(&cmd.args)
        .current_dir(root)
        .status()
        .map_err(|error| format!("cannot run `{shown}`: {error}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("`{shown}` exited with {status}"))
    }
}

/// Entry point of `cargo xtask check`. With `receipt`, the run is recorded
/// there whether it passes or fails.
pub fn run(root: PathBuf, receipt: Option<PathBuf>) -> ExitCode {
    let before = receipt.as_ref().map(|_| {
        (
            receipt::GitState::read(&root),
            receipt::rustc_version(&root),
        )
    });
    let outcomes = run_steps(&root, &steps());
    let mut code = match failure(&outcomes) {
        None => {
            println!("check passed");
            ExitCode::SUCCESS
        }
        Some((step, detail)) => {
            eprintln!("{detail}");
            eprintln!("check failed at step {step}");
            ExitCode::FAILURE
        }
    };
    if let (Some(path), Some((before, rustc))) = (receipt, before) {
        let after = receipt::GitState::read(&root);
        let text = receipt::render(
            &before,
            &after,
            rustc.as_deref(),
            &outcomes,
            &receipt::Environment::read(),
        );
        match receipt::write(&path, &text) {
            Ok(()) => println!("receipt written to {}", path.display()),
            Err(error) => {
                eprintln!("cannot write the receipt {}: {error}", path.display());
                code = ExitCode::FAILURE;
            }
        }
    }
    code
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::*;

    const ORDER: [&str; 11] = [
        "fmt",
        "clippy",
        "test",
        "docs",
        "commits",
        "workflows",
        "kalyx-fmt",
        "kalyx-clippy",
        "kalyx-test",
        "kalyx-allocation",
        "guard",
    ];

    #[test]
    fn steps_run_in_the_documented_order() {
        let names: Vec<&str> = steps().iter().map(|step| step.name).collect();
        assert_eq!(names, ORDER);
    }

    #[test]
    fn command_steps_cover_the_xtask_workspace_the_package_and_the_allocation_check() {
        let mut seen = Vec::new();
        for step in steps() {
            if let Action::Commands(commands) = step.action {
                for cmd in commands {
                    let at = cmd.args.iter().position(|arg| arg == "--manifest-path");
                    let at = at.expect("each command names a manifest");
                    seen.push((step.name, cmd.args[at + 1].clone()));
                }
            }
        }
        assert_eq!(
            seen,
            [
                ("fmt", MANIFEST.to_string()),
                ("clippy", MANIFEST.to_string()),
                ("test", MANIFEST.to_string()),
                ("kalyx-fmt", PACKAGE_MANIFEST.to_string()),
                ("kalyx-clippy", PACKAGE_MANIFEST.to_string()),
                ("kalyx-test", PACKAGE_MANIFEST.to_string()),
                ("kalyx-allocation", ALLOCATION_MANIFEST.to_string()),
                ("kalyx-allocation", ALLOCATION_MANIFEST.to_string()),
                ("kalyx-allocation", ALLOCATION_MANIFEST.to_string()),
                ("kalyx-allocation", ALLOCATION_MANIFEST.to_string()),
            ]
        );
    }

    /// The arguments of each command of the step `name`.
    fn commands_of(name: &str) -> Vec<Vec<String>> {
        let steps = steps();
        let step = steps.iter().find(|step| step.name == name).unwrap();
        match &step.action {
            Action::Commands(commands) => commands.iter().map(|cmd| cmd.args.clone()).collect(),
            Action::Internal(_) => panic!("{name} runs a command"),
        }
    }

    /// The arguments of the single command of the step `name`.
    fn args_of(name: &str) -> Vec<String> {
        let commands = commands_of(name);
        assert_eq!(commands.len(), 1, "{name}");
        commands[0].clone()
    }

    #[test]
    fn clippy_denies_warnings_and_cargo_uses_the_lock_file() {
        for (fmt, clippy, test) in [
            ("fmt", "clippy", "test"),
            ("kalyx-fmt", "kalyx-clippy", "kalyx-test"),
        ] {
            let warnings = ["--".to_string(), "-D".to_string(), "warnings".to_string()];
            assert!(args_of(clippy).ends_with(&warnings), "{clippy}");
            assert!(args_of(clippy).contains(&"--all-targets".to_string()));
            assert!(args_of(clippy).contains(&"--locked".to_string()));
            assert!(args_of(test).contains(&"--locked".to_string()));
            assert!(args_of(fmt).contains(&"--check".to_string()));
        }
    }

    // The allocation step format-checks the check crate, lints it with
    // warnings as errors, runs the tests of its verdict and then runs it,
    // each with its own lock file.
    #[test]
    fn the_allocation_step_checks_and_runs_the_allocation_crate() {
        let commands = commands_of("kalyx-allocation");
        let subcommands: Vec<&str> = commands.iter().map(|args| args[0].as_str()).collect();
        assert_eq!(subcommands, ["fmt", "clippy", "test", "run"]);
        assert!(commands[0].contains(&"--check".to_string()));
        let warnings = ["--".to_string(), "-D".to_string(), "warnings".to_string()];
        assert!(commands[1].ends_with(&warnings));
        assert!(commands[1].contains(&"--all-targets".to_string()));
        assert!(commands[1].contains(&"--locked".to_string()));
        assert!(commands[2].contains(&"--locked".to_string()));
        assert!(commands[3].contains(&"--locked".to_string()));
    }

    /// The real step list with `failing` replaced by a failing action and
    /// every other step replaced by one that records that it ran and adds a
    /// fact.
    fn with_failure(failing: &str, ran: &Rc<RefCell<Vec<&'static str>>>) -> Vec<Step> {
        steps()
            .into_iter()
            .map(|step| {
                let name = step.name;
                let action = if name == failing {
                    match step.action {
                        // A real process that exits with a non-zero status.
                        Action::Commands(_) => Action::Commands(vec![Cmd {
                            program: "sh".into(),
                            args: vec!["-c".into(), "exit 3".into()],
                        }]),
                        Action::Internal(_) => Action::Internal(Box::new(|_, facts| {
                            facts.push(("seen".to_string(), "before failing".to_string()));
                            Err("forced failure".to_string())
                        })),
                    }
                } else {
                    let ran = Rc::clone(ran);
                    Action::Internal(Box::new(move |_, facts| {
                        ran.borrow_mut().push(name);
                        facts.push(("ran".to_string(), name.to_string()));
                        Ok(())
                    }))
                };
                Step { name, action }
            })
            .collect()
    }

    fn assert_fails_at(failing: &'static str) {
        let ran = Rc::new(RefCell::new(Vec::new()));
        let steps = with_failure(failing, &ran);
        let outcomes = run_steps(Path::new("."), &steps);
        let (step, _) = failure(&outcomes).expect("the check fails");
        assert_eq!(step, failing);
        let failed_at = ORDER.iter().position(|name| *name == failing).unwrap();
        assert_eq!(
            *ran.borrow(),
            ORDER[..failed_at],
            "steps after the failure must not run"
        );
        let names: Vec<&str> = outcomes.iter().map(|outcome| outcome.step).collect();
        assert_eq!(names, ORDER, "every step has an outcome");
        for (index, outcome) in outcomes.iter().enumerate() {
            match index.cmp(&failed_at) {
                std::cmp::Ordering::Less => {
                    assert_eq!(outcome.status, Status::Passed);
                    assert_eq!(
                        outcome.facts,
                        [("ran".to_string(), outcome.step.to_string())]
                    );
                }
                std::cmp::Ordering::Equal => {
                    assert!(matches!(outcome.status, Status::Failed(_)), "{outcome:?}");
                }
                std::cmp::Ordering::Greater => {
                    assert_eq!(outcome.status, Status::NotRun);
                    assert_eq!(outcome.duration, Duration::ZERO);
                    assert!(outcome.facts.is_empty());
                }
            }
        }
    }

    #[test]
    fn a_format_failure_stops_the_check() {
        assert_fails_at("fmt");
    }

    #[test]
    fn a_clippy_failure_stops_the_check() {
        assert_fails_at("clippy");
    }

    #[test]
    fn a_test_failure_stops_the_check() {
        assert_fails_at("test");
    }

    #[test]
    fn a_docs_failure_stops_the_check() {
        assert_fails_at("docs");
    }

    #[test]
    fn a_commits_failure_stops_the_check() {
        assert_fails_at("commits");
    }

    #[test]
    fn a_workflows_failure_stops_the_check() {
        assert_fails_at("workflows");
    }

    #[test]
    fn a_package_format_failure_stops_the_check() {
        assert_fails_at("kalyx-fmt");
    }

    #[test]
    fn a_package_clippy_failure_stops_the_check() {
        assert_fails_at("kalyx-clippy");
    }

    #[test]
    fn a_package_test_failure_stops_the_check() {
        assert_fails_at("kalyx-test");
    }

    #[test]
    fn an_allocation_failure_stops_the_check() {
        assert_fails_at("kalyx-allocation");
    }

    #[test]
    fn a_guard_failure_fails_the_check_after_every_other_step() {
        assert_fails_at("guard");
    }

    #[test]
    fn a_failing_step_keeps_the_facts_it_added() {
        let ran = Rc::new(RefCell::new(Vec::new()));
        let outcomes = run_steps(Path::new("."), &with_failure("commits", &ran));
        let commits = &outcomes[ORDER.iter().position(|name| *name == "commits").unwrap()];
        assert_eq!(
            commits.facts,
            [("seen".to_string(), "before failing".to_string())]
        );
        assert_eq!(commits.status, Status::Failed("forced failure".to_string()));
    }
}

/// The kalyx steps run for real on a temporary copy of the package: its
/// manifest with the lint configuration, its lock file, `clippy.toml`,
/// `rust-toolchain.toml` and the crate attributes of `src/lib.rs`, with a
/// minimal library and program.
#[cfg(test)]
mod package_tests {
    use std::fs;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::*;
    use crate::repo;

    /// The files copied unchanged from the repository root.
    const COPIED: [&str; 4] = [
        "Cargo.toml",
        "Cargo.lock",
        "clippy.toml",
        "rust-toolchain.toml",
    ];

    /// Library code that the rules allow: an `#[allow]` with its reason, and
    /// `unwrap`, `expect` and `panic!` in tests.
    const ALLOWED: &str = r#"
#[allow(dead_code, reason = "only the tests call it")]
fn half(value: u32) -> Option<u32> {
    value.checked_div(2)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn halves() {
        assert_eq!(half(4).unwrap(), 2);
        assert_eq!(half(6).expect("six halves"), 3);
        if half(8) != Some(4) {
            panic!("eight halves to four");
        }
    }
}
"#;

    /// A temporary copy of the package in the system temporary directory,
    /// removed when dropped. Each copy has a build directory of its own:
    /// copies share the package name and their files are written within
    /// moments of each other, so a shared build directory could take one
    /// copy's build for another's.
    struct Package {
        dir: PathBuf,
    }

    impl Package {
        fn new() -> Package {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let root = repo::root();
            let dir = std::env::temp_dir().join(format!(
                "kalyx-xtask-package-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            if dir.exists() {
                fs::remove_dir_all(&dir).unwrap();
            }
            fs::create_dir_all(dir.join("src")).unwrap();
            for name in COPIED {
                fs::copy(root.join(name), dir.join(name)).unwrap();
            }
            let lib = fs::read_to_string(root.join("src/lib.rs")).unwrap();
            let attributes: Vec<&str> =
                lib.lines().filter(|line| line.starts_with("#![")).collect();
            for required in [
                "#![forbid(unsafe_code)]",
                "#![deny(clippy::float_arithmetic)]",
            ] {
                assert!(
                    attributes.contains(&required),
                    "src/lib.rs lacks {required}"
                );
            }
            let package = Package { dir };
            package.write(
                "src/lib.rs",
                &format!(
                    "//! A minimal copy of the kalyx library.\n\n{}\n",
                    attributes.join("\n")
                ),
            );
            package.write(
                "src/main.rs",
                "//! A minimal copy of the kalyx program.\n\nfn main() {}\n",
            );
            package
        }

        fn write(&self, path: &str, text: &str) {
            fs::write(self.dir.join(path), text).unwrap();
        }

        fn append(&self, path: &str, text: &str) {
            let mut content = fs::read_to_string(self.dir.join(path)).unwrap();
            content.push_str(text);
            self.write(path, &content);
        }

        /// Runs the commands of the step `name` in the copy, as the check
        /// runs them in the repository root; whether every command passed,
        /// and the output.
        fn run(&self, name: &str) -> (bool, String) {
            let steps = steps();
            let step = steps.iter().find(|step| step.name == name).unwrap();
            let Action::Commands(commands) = &step.action else {
                panic!("{name} runs commands");
            };
            let mut text = String::new();
            for cmd in commands {
                let output = Command::new(&cmd.program)
                    .args(&cmd.args)
                    .current_dir(&self.dir)
                    .env("CARGO_TARGET_DIR", self.dir.join("target"))
                    .output()
                    .expect("cargo runs");
                text.push_str(&String::from_utf8_lossy(&output.stdout));
                text.push_str(&String::from_utf8_lossy(&output.stderr));
                if !output.status.success() {
                    return (false, text);
                }
            }
            (true, text)
        }

        fn passes(&self, name: &str) {
            let (passed, output) = self.run(name);
            assert!(passed, "{name} failed:\n{output}");
        }

        /// Asserts that the step `name` fails and that its output names
        /// each of `reasons`, with `-` read as `_`.
        fn fails(&self, name: &str, reasons: &[&str]) {
            let (passed, output) = self.run(name);
            assert!(!passed, "{name} passed:\n{output}");
            let normalized = output.replace('-', "_");
            for reason in reasons {
                assert!(
                    normalized.contains(reason),
                    "{name} failed without naming `{reason}`:\n{output}"
                );
            }
        }
    }

    impl Drop for Package {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.dir);
        }
    }

    #[test]
    fn the_package_with_allowed_code_passes_every_package_step() {
        let package = Package::new();
        package.append("src/lib.rs", ALLOWED);
        package.passes("kalyx-fmt");
        package.passes("kalyx-clippy");
        package.passes("kalyx-test");
    }

    #[test]
    fn unformatted_code_fails_the_package_format_step() {
        let package = Package::new();
        package.append("src/lib.rs", "\npub fn one( )->u8{1}\n");
        package.fails("kalyx-fmt", &["Diff in"]);
    }

    #[test]
    fn each_explicit_panic_in_library_code_fails_the_package_clippy_step() {
        let package = Package::new();
        package.append(
            "src/lib.rs",
            r#"
pub fn denied(value: Option<u8>, kind: u8) -> u8 {
    match kind {
        0 => value.unwrap(),
        1 => value.expect("a value"),
        2 => panic!("no value"),
        3 => unreachable!(),
        4 => todo!(),
        _ => unimplemented!(),
    }
}
"#,
        );
        package.fails(
            "kalyx-clippy",
            &[
                "clippy::unwrap_used",
                "clippy::expect_used",
                "clippy::panic",
                "clippy::unreachable",
                "clippy::todo",
                "clippy::unimplemented",
            ],
        );
    }

    #[test]
    fn an_allow_without_a_reason_fails_the_package_clippy_step() {
        let package = Package::new();
        package.append("src/lib.rs", "\n#[allow(dead_code)]\nfn unused() {}\n");
        package.fails("kalyx-clippy", &["clippy::allow_attributes_without_reason"]);
    }

    #[test]
    fn a_failing_test_fails_the_package_test_step() {
        let package = Package::new();
        package.append(
            "src/lib.rs",
            r#"
#[cfg(test)]
mod tests {
    #[test]
    fn fails() {
        assert_eq!(2_u8.pow(2), 5, "a failing test");
    }
}
"#,
        );
        package.passes("kalyx-clippy");
        package.fails("kalyx-test", &["tests::fails"]);
    }

    #[test]
    fn unsafe_code_fails_in_the_library_and_in_the_program() {
        let package = Package::new();
        package.append(
            "src/lib.rs",
            "\npub fn read(value: &u8) -> u8 {\n    unsafe { *std::ptr::from_ref(value) }\n}\n",
        );
        package.fails("kalyx-clippy", &["unsafe_code"]);
        let package = Package::new();
        package.write(
            "src/main.rs",
            "fn main() {\n    let value = 1_u8;\n    let _copy = unsafe { *std::ptr::from_ref(&value) };\n}\n",
        );
        package.fails("kalyx-clippy", &["unsafe_code"]);
    }

    #[test]
    fn float_arithmetic_fails_in_the_library_and_in_the_program() {
        let package = Package::new();
        package.append(
            "src/lib.rs",
            "\npub fn double(value: f64) -> f64 {\n    value * 2.0\n}\n",
        );
        package.fails("kalyx-clippy", &["clippy::float_arithmetic"]);
        let package = Package::new();
        package.write(
            "src/main.rs",
            "fn main() {\n    let value: f64 = 1.5;\n    let _sum = value + 1.0;\n}\n",
        );
        package.fails("kalyx-clippy", &["clippy::float_arithmetic"]);
    }

    #[test]
    fn a_libm_function_fails_the_package_clippy_step_whatever_the_path() {
        let package = Package::new();
        package.append(
            "src/lib.rs",
            r#"
type Float = f64;

pub fn through_an_alias(value: Float) -> Float {
    Float::sin(value)
}

pub fn through_a_method(value: f32) -> f32 {
    value.cbrt()
}

pub fn through_a_trait<T: Copy>(value: T, apply: fn(T) -> T) -> T {
    apply(value)
}

pub fn through_a_function_value(value: f64) -> f64 {
    through_a_trait(value, f64::exp)
}
"#,
        );
        package.fails(
            "kalyx-clippy",
            &[
                "clippy::disallowed_methods",
                "disallowed method `f64::sin`",
                "disallowed method `f32::cbrt`",
                "disallowed method `f64::exp`",
            ],
        );
    }

    #[test]
    fn clippy_disallows_every_libm_function_of_the_floats_and_their_traits() {
        let config = fs::read_to_string(repo::root().join("clippy.toml")).unwrap();
        for owner in [
            "f32",
            "f64",
            "num_traits::float::Float",
            "num_traits::real::Real",
        ] {
            for name in crate::scan::LIBM {
                assert!(
                    config.contains(&format!("path = \"{owner}::{name}\"")),
                    "clippy.toml does not disallow {owner}::{name}"
                );
            }
        }
    }
}
