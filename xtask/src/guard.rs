//! The guard step: the kalyx package keeps to the rules of its library code
//! that the compiler and Clippy do not check.
//!
//! The step reads the files that Git tracks and fails with every finding,
//! each with its file and line:
//!
//! - the non-test code of every tracked `.rs` file outside the directories
//!   of [`NOT_PACKAGE`], such as the files below `src/` and a build script,
//!   passes the source scan of [`scan`](crate::scan), which rejects threads,
//!   hash containers, `RandomState`, `SystemTime`, `thread_local!`,
//!   `catch_unwind`, `static mut`, the transcendental functions of the
//!   platform math library, constructing `Context` outside the command entry
//!   and the program, and `std` paths that [`STD_PATHS`] does not permit.
//!   The file of a module that only test code declares, as
//!   `#[cfg(test)] mod name;`, and the files of its submodules are skipped;
//!   a file that a scanned file declares as non-test code is scanned. Such a
//!   `.rs` entry that is a symbolic link, a submodule or not UTF-8 is a
//!   finding, since it cannot be scanned;
//! - `Cargo.lock` holds only the package itself and the packages that
//!   [`CRATES`] names, and never a package of [`DENIED_CRATES`]; so does the
//!   lock file of each check crate of [`CHECK_CRATES`], which may also hold
//!   the check crate itself, and a manifest or lock file under `checks/`
//!   outside those crates is a finding;
//! - the `license` field of the package in `Cargo.toml` is exactly
//!   [`LICENSE`], and its `[profile.release]` table sets
//!   `overflow-checks = true`.
//!
//! # Allow lists
//!
//! An allow list holds one entry per line; blank lines and lines that start
//! with `#` are skipped. An entry of [`STD_PATHS`] is a path such as
//! `std::io::stdin` of at least two segments. It permits a `std` path that
//! equals it or lies below it: `std::fmt` permits `std::fmt::Display`, and
//! `std::io::Write` permits `std::io::Write::flush` but not
//! `std::io::WriteFmt`. An entry may not name, contain or lie below a path
//! of [`DENIED_STD`]. An entry of [`CRATES`] is a package name.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use crate::check::Facts;
use crate::repo::{Entry, Tree};
use crate::scan;

/// The allow list of `std` paths, relative to the repository root.
pub const STD_PATHS: &str = "guard/std-paths.txt";

/// The allow list of packages in `Cargo.lock`.
pub const CRATES: &str = "guard/crates.txt";

/// The license that the package must state.
pub const LICENSE: &str = "MIT";

/// The directories whose Rust files are not code of the package and are not
/// read: the repository checks, in `xtask/` and the check crate of
/// [`CHECK_CRATES`], and the integration tests, benchmarks and examples,
/// which are test code. Any other file under `checks/` is read.
pub const NOT_PACKAGE: [&str; 5] = [
    "xtask/",
    "checks/allocation/",
    "tests/",
    "benches/",
    "examples/",
];

/// The check crates: workspaces of their own outside the package, each
/// depending on the package by path. The lock file of each may hold only the
/// package, the check crate itself and the packages that [`CRATES`] names.
pub const CHECK_CRATES: [&str; 1] = ["checks/allocation"];

/// `std` paths that no entry of [`STD_PATHS`] may name, contain or lie
/// below.
pub const DENIED_STD: [&str; 10] = [
    "std::thread",
    "std::thread_local",
    "std::collections::HashMap",
    "std::collections::HashSet",
    "std::collections::hash_map",
    "std::collections::hash_set",
    "std::hash::RandomState",
    "std::time::SystemTime",
    "std::time::UNIX_EPOCH",
    "std::panic::catch_unwind",
];

/// Packages that `Cargo.lock` may never hold, even when [`CRATES`] names
/// them: each name, and for a family every name that starts with it and
/// `-` or `_`.
pub const DENIED_CRATES: [(&str, bool); 4] = [
    ("getrandom", false),
    ("rand", true),
    ("rayon", true),
    ("crossbeam", true),
];

/// What the guard read and found.
#[derive(Debug, Default)]
pub struct Report {
    /// The source files that the scan read.
    pub files: Vec<String>,
    /// The number of entries of [`STD_PATHS`] and [`CRATES`].
    pub std_paths: usize,
    pub crates: usize,
    pub problems: Vec<String>,
}

/// The guard step on the tracked files; what it read becomes facts.
pub fn run(root: &Path, facts: &mut Facts) -> Result<(), String> {
    let report = check(&Tree::load(root)?);
    println!(
        "guard: {} source files, {} entries in {STD_PATHS}, {} entries in {CRATES}",
        report.files.len(),
        report.std_paths,
        report.crates
    );
    facts.push(("files".to_string(), report.files.join(", ")));
    facts.push(("std_paths".to_string(), report.std_paths.to_string()));
    facts.push(("crates".to_string(), report.crates.to_string()));
    if report.problems.is_empty() {
        Ok(())
    } else {
        Err(report.problems.join("\n"))
    }
}

/// Every guard problem in `tree`.
pub fn check(tree: &Tree) -> Report {
    let mut report = Report::default();
    let std_paths = match tree.text(STD_PATHS) {
        Some(text) => std_entries(text, &mut report.problems),
        None => {
            report.problems.push(format!("{STD_PATHS} is missing"));
            Vec::new()
        }
    };
    report.std_paths = std_paths.len();
    let crates = match tree.text(CRATES) {
        Some(text) => crate_entries(text, &mut report.problems),
        None => {
            report.problems.push(format!("{CRATES} is missing"));
            Vec::new()
        }
    };
    report.crates = crates.len();
    let manifest = tree.text("Cargo.toml").unwrap_or_default();
    check_license(manifest, &mut report.problems);
    check_release_profile(manifest, &mut report.problems);
    let package = package_field(manifest, "name");
    match tree.text("Cargo.lock") {
        Some(lock) => {
            let own: Vec<&str> = package.iter().map(String::as_str).collect();
            check_lock("Cargo.lock", lock, &own, &crates, &mut report.problems);
        }
        None => report.problems.push("Cargo.lock is missing".to_string()),
    }
    for dir in CHECK_CRATES {
        check_crate_lock(tree, dir, package.as_deref(), &crates, &mut report.problems);
    }
    check_unlisted_crates(tree, &mut report.problems);
    check_sources(tree, &std_paths, &mut report);
    report
}

/// Reports a manifest or a lock file under `checks/` that is not one of a
/// check crate of [`CHECK_CRATES`], whose sources the source scan would
/// skip and whose lock file nothing would check.
fn check_unlisted_crates(tree: &Tree, problems: &mut Vec<String>) {
    for (path, _) in tree.entries() {
        let Some((dir, file)) = path.rsplit_once('/') else {
            continue;
        };
        if path.starts_with("checks/")
            && (file == "Cargo.toml" || file == "Cargo.lock")
            && !CHECK_CRATES.contains(&dir)
        {
            problems.push(format!(
                "{path}: a crate under checks/ that is not a listed check crate"
            ));
        }
    }
}

/// Checks the lock file of the check crate in `dir`, whose own packages are
/// the check crate, by the name in its manifest, and `package`, the package
/// at the root, which it depends on by path.
fn check_crate_lock(
    tree: &Tree,
    dir: &str,
    package: Option<&str>,
    crates: &[String],
    problems: &mut Vec<String>,
) {
    let path = format!("{dir}/Cargo.lock");
    let Some(lock) = tree.text(&path) else {
        problems.push(format!("{path} is missing"));
        return;
    };
    let manifest = tree.text(&format!("{dir}/Cargo.toml")).unwrap_or_default();
    let name = package_field(manifest, "name");
    let own: Vec<&str> = name.as_deref().into_iter().chain(package).collect();
    check_lock(&path, lock, &own, crates, problems);
}

/// Whether the allow list `entries` permits the `std` path `path`.
pub fn std_allows(entries: &[String], path: &str) -> bool {
    entries.iter().any(|entry| {
        path.strip_prefix(entry.as_str())
            .is_some_and(|rest| rest.is_empty() || rest.starts_with("::"))
    })
}

/// The entries of an allow list with their line numbers.
fn entries(text: &str) -> Vec<(usize, &str)> {
    text.lines()
        .enumerate()
        .map(|(index, line)| (index + 1, line.trim()))
        .filter(|(_, line)| !line.is_empty() && !line.starts_with('#'))
        .collect()
}

fn is_identifier(text: &str) -> bool {
    let mut chars = text.chars();
    chars
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
        && chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

/// The valid entries of the std allow list; the others become problems.
fn std_entries(text: &str, problems: &mut Vec<String>) -> Vec<String> {
    let mut valid: Vec<String> = Vec::new();
    for (line, entry) in entries(text) {
        let segments: Vec<&str> = entry.split("::").collect();
        let problem = if segments[0] != "std"
            || segments.len() < 2
            || !segments.iter().all(|segment| is_identifier(segment))
        {
            Some("is not a path `std::...` of at least two segments".to_string())
        } else if valid.iter().any(|seen| seen == entry) {
            Some("is listed twice".to_string())
        } else {
            DENIED_STD
                .iter()
                .find(|denied| {
                    std_allows(&[entry.to_string()], denied)
                        || std_allows(&[denied.to_string()], entry)
                })
                .map(|denied| format!("would permit `{denied}`, which is never allowed"))
        };
        match problem {
            Some(problem) => problems.push(format!("{STD_PATHS}:{line}: `{entry}` {problem}")),
            None => valid.push(entry.to_string()),
        }
    }
    valid
}

/// The valid entries of the package allow list; the others become
/// problems.
fn crate_entries(text: &str, problems: &mut Vec<String>) -> Vec<String> {
    let mut valid: Vec<String> = Vec::new();
    for (line, entry) in entries(text) {
        if !entry
            .chars()
            .all(|c| c == '-' || c == '_' || c.is_ascii_alphanumeric())
        {
            problems.push(format!("{CRATES}:{line}: `{entry}` is not a package name"));
        } else if valid.iter().any(|seen| seen == entry) {
            problems.push(format!("{CRATES}:{line}: `{entry}` is listed twice"));
        } else {
            valid.push(entry.to_string());
        }
    }
    valid
}

/// Whether `name` is a package that `Cargo.lock` may never hold.
pub fn denied_crate(name: &str) -> bool {
    DENIED_CRATES.iter().any(|(denied, family)| {
        name == *denied
            || (*family
                && name
                    .strip_prefix(denied)
                    .is_some_and(|rest| rest.starts_with(['-', '_'])))
    })
}

/// The raw value of `key` in the table `[table]` of a manifest, written as
/// `key = value` on one line of that table.
fn table_value<'a>(manifest: &'a str, table: &str, key: &str) -> Option<&'a str> {
    let header = format!("[{table}]");
    let mut in_table = false;
    for line in manifest.lines() {
        let line = line.trim();
        if line.starts_with('[') {
            in_table = line
                .strip_prefix(header.as_str())
                .is_some_and(|rest| rest.trim().is_empty() || rest.trim().starts_with('#'));
            continue;
        }
        if !in_table {
            continue;
        }
        let Some((name, value)) = line.split_once('=') else {
            continue;
        };
        if name.trim() == key {
            return Some(value.trim());
        }
    }
    None
}

/// The string value of `key` in the `[package]` table of a manifest, when
/// it is a basic or literal string on one line.
fn package_field(manifest: &str, key: &str) -> Option<String> {
    let value = table_value(manifest, "package", key)?;
    let quote = value.chars().next().filter(|c| *c == '"' || *c == '\'')?;
    let rest = &value[1..];
    let end = rest.find(quote)?;
    let tail = rest[end + 1..].trim();
    (tail.is_empty() || tail.starts_with('#')).then(|| rest[..end].to_string())
}

fn check_release_profile(manifest: &str, problems: &mut Vec<String>) {
    let value = table_value(manifest, "profile.release", "overflow-checks").map(|value| {
        value
            .split_once('#')
            .map_or(value, |(value, _)| value)
            .trim()
    });
    if value != Some("true") {
        problems.push(
            "Cargo.toml: the `[profile.release]` table must set `overflow-checks = true`"
                .to_string(),
        );
    }
}

fn check_license(manifest: &str, problems: &mut Vec<String>) {
    match package_field(manifest, "license") {
        Some(license) if license == LICENSE => {}
        Some(license) => problems.push(format!(
            "Cargo.toml: the license of the package is `{license}`, not `{LICENSE}`"
        )),
        None => problems.push(format!(
            "Cargo.toml: the package states no license; it must be `{LICENSE}`"
        )),
    }
}

/// A package of `Cargo.lock`: its name, whether it has a `source` (a
/// registry or Git package) and the line of its `[[package]]` header.
#[derive(Debug)]
struct Locked {
    name: Option<String>,
    source: bool,
    line: usize,
}

fn locked_packages(lock: &str) -> Vec<Locked> {
    let mut packages: Vec<Locked> = Vec::new();
    let mut current = false;
    for (index, line) in lock.lines().enumerate() {
        let line = line.trim();
        if line.starts_with('[') {
            current = line == "[[package]]";
            if current {
                packages.push(Locked {
                    name: None,
                    source: false,
                    line: index + 1,
                });
            }
            continue;
        }
        let Some(package) = packages.last_mut().filter(|_| current) else {
            continue;
        };
        if let Some((key, value)) = line.split_once('=') {
            match key.trim() {
                "name" => package.name = Some(value.trim().trim_matches('"').to_string()),
                "source" => package.source = true,
                _ => {}
            }
        }
    }
    packages
}

/// Checks the packages of the lock file `lock` at `path` against the allow
/// list `crates`. The packages named in `own`, without a source, are the
/// packages of the repository: the package itself and, in the lock file of a
/// check crate, the check crate.
fn check_lock(path: &str, lock: &str, own: &[&str], crates: &[String], problems: &mut Vec<String>) {
    for package in locked_packages(lock) {
        let Some(name) = package.name else {
            problems.push(format!("{path}:{}: a package without a name", package.line));
            continue;
        };
        if denied_crate(&name) {
            problems.push(format!(
                "{path}:{}: package `{name}` is never allowed, even when {CRATES} names it",
                package.line
            ));
        } else if !(own.contains(&name.as_str()) && !package.source) && !crates.contains(&name) {
            problems.push(format!(
                "{path}:{}: package `{name}` is not in {CRATES}",
                package.line
            ));
        }
    }
}

/// Whether the module `module`, a path without the extension, is held by
/// the file `path` or lies below it.
fn module_holds(module: &str, path: &str) -> bool {
    path.strip_prefix(module)
        .is_some_and(|rest| rest == ".rs" || rest.starts_with('/'))
}

/// Scans the tracked Rust files of the package, except the files that only
/// test code declares.
fn check_sources(tree: &Tree, std_paths: &[String], report: &mut Report) {
    let allowed = |path: &str| std_allows(std_paths, path);
    let mut results = BTreeMap::new();
    let mut test_modules = BTreeSet::new();
    for (path, entry) in tree.entries() {
        if !path.ends_with(".rs") || NOT_PACKAGE.iter().any(|dir| path.starts_with(dir)) {
            continue;
        }
        let text = match entry {
            Entry::File(bytes) => std::str::from_utf8(bytes).ok(),
            Entry::Symlink | Entry::Submodule => None,
        };
        let Some(text) = text else {
            report.problems.push(format!(
                "{path}: a symbolic link, a submodule or not UTF-8, so the guard cannot scan it"
            ));
            continue;
        };
        let result = scan::scan(path, text, &allowed);
        if let Ok(scanned) = &result {
            test_modules.extend(scanned.test_modules.iter().cloned());
        }
        results.insert(path, result);
    }
    // A file is scanned unless a test module holds it; a file that a
    // scanned file declares as a non-test module is scanned too, as when the
    // library declares a module only for its tests and the program declares
    // it for itself.
    let mut scanned: BTreeSet<&str> = results
        .keys()
        .copied()
        .filter(|path| !test_modules.iter().any(|module| module_holds(module, path)))
        .collect();
    loop {
        let declared: Vec<&str> = scanned
            .iter()
            .filter_map(|path| results.get(path)?.as_ref().ok())
            .flat_map(|found| &found.modules)
            .flat_map(|module| [format!("{module}.rs"), format!("{module}/mod.rs")])
            .filter_map(|file| results.get_key_value(file.as_str()).map(|(path, _)| *path))
            .filter(|path| !scanned.contains(path))
            .collect();
        if declared.is_empty() {
            break;
        }
        scanned.extend(declared);
    }
    for (path, result) in results {
        if !scanned.contains(path) {
            continue;
        }
        report.files.push(path.to_string());
        let findings = match result {
            Ok(scanned) => scanned.findings,
            Err(finding) => vec![finding],
        };
        for finding in findings {
            report
                .problems
                .push(format!("{path}:{}: {}", finding.line, finding.message));
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::repo;

    const MANIFEST: &str = "[package]\nname = \"kalyx\"\nversion = \"0.1.0\"\nlicense = \"MIT\"\n\n[profile.release]\noverflow-checks = true\n";
    const LOCK: &str = "version = 4\n\n[[package]]\nname = \"kalyx\"\nversion = \"0.1.0\"\ndependencies = [\n \"num-traits\",\n]\n\n[[package]]\nname = \"num-traits\"\nversion = \"0.2.19\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n";
    const CHECK_MANIFEST: &str = "[package]\nname = \"kalyx-allocation-check\"\nversion = \"0.0.0\"\n\n[workspace]\n\n[dependencies]\nkalyx = { path = \"../..\" }\n";
    const CHECK_LOCK_PATH: &str = "checks/allocation/Cargo.lock";
    const CHECK_LOCK: &str = "version = 4\n\n[[package]]\nname = \"kalyx\"\nversion = \"0.1.0\"\ndependencies = [\n \"num-traits\",\n]\n\n[[package]]\nname = \"kalyx-allocation-check\"\nversion = \"0.0.0\"\ndependencies = [\n \"kalyx\",\n]\n\n[[package]]\nname = \"num-traits\"\nversion = \"0.2.19\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n";
    const STD: &str = "# The list.\n\nstd::fmt\nstd::io::stdin\nstd::process::ExitCode\n";
    const LIB: &str = "use std::fmt;\n\npub fn f() -> fmt::Result {\n    Ok(())\n}\n";

    /// A valid package, with `changes` replacing or adding files.
    fn tree(changes: &[(&str, &str)]) -> Tree {
        let mut files = vec![
            ("Cargo.toml", MANIFEST),
            ("Cargo.lock", LOCK),
            (STD_PATHS, STD),
            (CRATES, "# Packages.\nnum-traits\n"),
            ("src/lib.rs", LIB),
            (
                "src/main.rs",
                "use std::process::ExitCode;\n\nfn main() -> ExitCode {\n    ExitCode::SUCCESS\n}\n",
            ),
            ("checks/allocation/Cargo.toml", CHECK_MANIFEST),
            (CHECK_LOCK_PATH, CHECK_LOCK),
        ];
        for (path, text) in changes {
            files.retain(|(existing, _)| existing != path);
            files.push((path, text));
        }
        Tree::from_files(&files)
    }

    fn problems(changes: &[(&str, &str)]) -> Vec<String> {
        check(&tree(changes)).problems
    }

    #[test]
    fn a_valid_package_passes_and_its_counts_are_reported() {
        let report = check(&tree(&[]));
        assert_eq!(report.problems, Vec::<String>::new());
        assert_eq!(report.files, ["src/lib.rs", "src/main.rs"]);
        assert_eq!((report.std_paths, report.crates), (3, 1));
    }

    #[test]
    fn reports_every_finding_with_its_file_and_line() {
        let found = problems(&[
            (
                "src/lib.rs",
                "pub type Map = HashMap<u8, u8>;\n\npub fn f(x: f64) -> f64 {\n    x.sin()\n}\n",
            ),
            ("src/eval.rs", "use std::fs;\n"),
        ]);
        assert_eq!(
            found,
            [
                "src/eval.rs:1: std path `std::fs` is not in guard/std-paths.txt",
                "src/lib.rs:1: `HashMap` is not allowed in non-test code",
                "src/lib.rs:4: .sin( calls a transcendental function of the platform math library",
            ]
        );
    }

    #[test]
    fn rejects_a_std_path_outside_the_list() {
        assert_eq!(
            problems(&[("src/lib.rs", "use std::io::Read;\n")]),
            ["src/lib.rs:1: std path `std::io::Read` is not in guard/std-paths.txt"]
        );
    }

    #[test]
    fn the_std_list_permits_a_path_and_what_lies_below_it() {
        let entries = ["std::fmt".to_string(), "std::io::Write".to_string()];
        assert!(std_allows(&entries, "std::fmt"));
        assert!(std_allows(&entries, "std::fmt::Display"));
        assert!(std_allows(&entries, "std::io::Write::flush"));
        assert!(!std_allows(&entries, "std::io::WriteFmt"));
        assert!(!std_allows(&entries, "std::io"));
        assert!(!std_allows(&entries, "std::fmtx"));
    }

    #[test]
    fn rejects_invalid_std_list_entries() {
        let list = "std::fmt\nstd::fmt\nstd\ncore::fmt\nstd::io::\nstd::io stdin\nstd::thread::sleep\nstd::collections\nstd::time\nstd::panic\nstd::hash\nstd::thread_local\nstd::process::ExitCode\n";
        let found = problems(&[(STD_PATHS, list)]);
        let expected = [
            "guard/std-paths.txt:2: `std::fmt` is listed twice",
            "guard/std-paths.txt:3: `std` is not a path",
            "guard/std-paths.txt:4: `core::fmt` is not a path",
            "guard/std-paths.txt:5: `std::io::` is not a path",
            "guard/std-paths.txt:6: `std::io stdin` is not a path",
            "guard/std-paths.txt:7: `std::thread::sleep` would permit `std::thread`",
            "guard/std-paths.txt:8: `std::collections` would permit `std::collections::HashMap`",
            "guard/std-paths.txt:9: `std::time` would permit `std::time::SystemTime`",
            "guard/std-paths.txt:10: `std::panic` would permit `std::panic::catch_unwind`",
            "guard/std-paths.txt:11: `std::hash` would permit `std::hash::RandomState`",
            "guard/std-paths.txt:12: `std::thread_local` would permit `std::thread_local`",
        ];
        assert_eq!(found.len(), expected.len(), "{found:?}");
        for (problem, start) in found.iter().zip(expected) {
            assert!(problem.starts_with(start), "{problem} / {start}");
        }
        assert_eq!(check(&tree(&[(STD_PATHS, list)])).std_paths, 2);
    }

    #[test]
    fn rejects_an_unlisted_package_in_the_lock_file() {
        let lock = format!(
            "{LOCK}\n[[package]]\nname = \"num-bigint\"\nversion = \"0.4.6\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n"
        );
        assert_eq!(
            problems(&[("Cargo.lock", &lock)]),
            ["Cargo.lock:15: package `num-bigint` is not in guard/crates.txt"]
        );
        assert_eq!(
            problems(&[("Cargo.lock", &lock), (CRATES, "num-traits\nnum-bigint\n")]),
            Vec::<String>::new()
        );
    }

    #[test]
    fn rejects_getrandom_in_the_lock_file_even_when_listed() {
        let lock = format!(
            "{LOCK}\n[[package]]\nname = \"getrandom\"\nversion = \"0.3.3\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n"
        );
        assert_eq!(
            problems(&[("Cargo.lock", &lock), (CRATES, "num-traits\ngetrandom\n")]),
            [
                "Cargo.lock:15: package `getrandom` is never allowed, even when guard/crates.txt names it"
            ]
        );
    }

    #[test]
    fn denies_the_rand_rayon_and_crossbeam_families() {
        for name in [
            "getrandom",
            "rand",
            "rand_core",
            "rand-chacha",
            "rayon",
            "rayon-core",
            "crossbeam",
            "crossbeam-utils",
            "crossbeam_channel",
        ] {
            assert!(denied_crate(name), "{name}");
        }
        for name in [
            "getrandom2",
            "random",
            "randomize",
            "rayons",
            "num-traits",
            "autocfg",
        ] {
            assert!(!denied_crate(name), "{name}");
        }
    }

    #[test]
    fn only_the_package_itself_needs_no_entry() {
        // A registry package that has the name of the package is not the
        // package itself.
        let lock = format!(
            "{LOCK}\n[[package]]\nname = \"kalyx\"\nversion = \"0.0.1\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n"
        );
        assert_eq!(
            problems(&[("Cargo.lock", &lock)]),
            ["Cargo.lock:15: package `kalyx` is not in guard/crates.txt"]
        );
    }

    #[test]
    fn the_lock_file_of_a_check_crate_holds_only_listed_packages() {
        let with = |extra: &str| format!("{CHECK_LOCK}{extra}");
        // The package and the check crate, without a source, need no entry.
        assert_eq!(problems(&[]), Vec::<String>::new());
        let unlisted = with(
            "\n[[package]]\nname = \"num-bigint\"\nversion = \"0.4.8\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n",
        );
        assert_eq!(
            problems(&[(CHECK_LOCK_PATH, &unlisted)]),
            ["checks/allocation/Cargo.lock:22: package `num-bigint` is not in guard/crates.txt"]
        );
        let denied = with(
            "\n[[package]]\nname = \"rand_core\"\nversion = \"0.9.0\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n",
        );
        assert_eq!(
            problems(&[
                (CHECK_LOCK_PATH, &denied),
                (CRATES, "num-traits\nrand_core\n")
            ]),
            [
                "checks/allocation/Cargo.lock:22: package `rand_core` is never allowed, even when guard/crates.txt names it"
            ]
        );
        // A registry package that has the name of the check crate is not the
        // check crate.
        let impostor = with(
            "\n[[package]]\nname = \"kalyx-allocation-check\"\nversion = \"9.9.9\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n",
        );
        assert_eq!(
            problems(&[(CHECK_LOCK_PATH, &impostor)]),
            [
                "checks/allocation/Cargo.lock:22: package `kalyx-allocation-check` is not in guard/crates.txt"
            ]
        );
    }

    #[test]
    fn a_check_crate_without_its_lock_file_is_a_finding() {
        let mut files: Vec<(&str, &str)> = vec![
            ("Cargo.toml", MANIFEST),
            ("Cargo.lock", LOCK),
            (STD_PATHS, STD),
            (CRATES, "num-traits\n"),
            ("src/lib.rs", LIB),
            ("checks/allocation/Cargo.toml", CHECK_MANIFEST),
        ];
        files.sort();
        assert_eq!(
            check(&Tree::from_files(&files)).problems,
            ["checks/allocation/Cargo.lock is missing"]
        );
    }

    #[test]
    fn rejects_invalid_package_list_entries() {
        assert_eq!(
            problems(&[(CRATES, "num-traits\nnum-traits\nnum traits\n")]),
            [
                "guard/crates.txt:2: `num-traits` is listed twice",
                "guard/crates.txt:3: `num traits` is not a package name",
            ]
        );
    }

    #[test]
    fn rejects_a_license_other_than_mit() {
        let with = |license: &str| MANIFEST.replace("license = \"MIT\"", license);
        assert_eq!(
            problems(&[("Cargo.toml", &with("license = \"MIT OR Apache-2.0\""))]),
            ["Cargo.toml: the license of the package is `MIT OR Apache-2.0`, not `MIT`"]
        );
        assert_eq!(
            problems(&[("Cargo.toml", &with("license = 'MIT' # the license"))]),
            Vec::<String>::new()
        );
        for manifest in [
            with(""),
            with("license.workspace = true"),
            with("license-file = \"LICENSE\""),
            with("") + "\n[package.metadata]\nlicense = \"MIT\"\n",
        ] {
            assert_eq!(
                problems(&[("Cargo.toml", &manifest)]),
                ["Cargo.toml: the package states no license; it must be `MIT`"],
                "{manifest}"
            );
        }
    }

    #[test]
    fn rejects_a_release_profile_without_overflow_checks() {
        let problem =
            ["Cargo.toml: the `[profile.release]` table must set `overflow-checks = true`"];
        let with = |profile: &str| {
            MANIFEST.replace("[profile.release]\noverflow-checks = true\n", profile)
        };
        for profile in [
            "",
            "[profile.release]\n",
            "[profile.release]\noverflow-checks = false\n",
            "[profile.release]\noverflow-checks = \"true\"\n",
            "[profile.dev]\noverflow-checks = true\n",
            "[profile.release.package.kalyx]\noverflow-checks = true\n",
            "[profile.release]\ndebug = true\n[workspace]\noverflow-checks = true\n",
        ] {
            assert_eq!(
                problems(&[("Cargo.toml", &with(profile))]),
                problem,
                "{profile}"
            );
        }
        for profile in [
            "[profile.release]\noverflow-checks = true # never wrap\n",
            "[profile.release] # the release build\nlto = true\noverflow-checks=true\n",
        ] {
            assert_eq!(
                problems(&[("Cargo.toml", &with(profile))]),
                Vec::<String>::new(),
                "{profile}"
            );
        }
    }

    #[test]
    fn rejects_missing_lists_and_lock_file() {
        let mut files: Vec<(&str, &str)> = vec![("Cargo.toml", MANIFEST), ("src/lib.rs", "")];
        files.sort();
        let report = check(&Tree::from_files(&files));
        assert_eq!(
            report.problems,
            [
                "guard/std-paths.txt is missing",
                "guard/crates.txt is missing",
                "Cargo.lock is missing",
                "checks/allocation/Cargo.lock is missing",
            ]
        );
    }

    #[test]
    fn skips_the_files_of_test_modules_only() {
        let denied = "pub type Map = HashMap<u8, u8>;\n";
        let report = check(&tree(&[
            (
                "src/lib.rs",
                "#[cfg(test)]\nmod tests;\nmod expr;\n#[cfg(test)]\n#[path = \"moved.rs\"]\nmod moved;\n",
            ),
            ("src/tests.rs", denied),
            ("src/tests/helpers.rs", denied),
            ("src/expr.rs", "#[cfg(test)]\nmod tests;\n"),
            ("src/expr/tests/mod.rs", denied),
            ("src/moved.rs", denied),
            ("src/testsuite.rs", denied),
            ("tests/integration.rs", denied),
        ]));
        assert_eq!(
            report.problems,
            [
                "src/moved.rs:1: `HashMap` is not allowed in non-test code",
                "src/testsuite.rs:1: `HashMap` is not allowed in non-test code",
            ]
        );
        assert_eq!(
            report.files,
            [
                "src/expr.rs",
                "src/lib.rs",
                "src/main.rs",
                "src/moved.rs",
                "src/testsuite.rs"
            ]
        );
    }

    #[test]
    fn scans_a_file_that_non_test_code_also_declares() {
        let denied = "pub type Map = HashMap<u8, u8>;\n";
        let report = check(&tree(&[
            (
                "src/lib.rs",
                "#[cfg(test)]\nmod util;\n#[cfg(test)]\nmod tests;\n",
            ),
            ("src/main.rs", "mod util;\n\nfn main() {}\n"),
            ("src/util.rs", "mod inner;\n#[cfg(test)]\nmod tests;\n"),
            ("src/util/inner.rs", denied),
            ("src/util/tests.rs", denied),
            ("src/tests.rs", "mod helpers;\n"),
            ("src/tests/helpers.rs", denied),
        ]));
        assert_eq!(
            report.problems,
            ["src/util/inner.rs:1: `HashMap` is not allowed in non-test code"]
        );
        assert_eq!(
            report.files,
            [
                "src/lib.rs",
                "src/main.rs",
                "src/util.rs",
                "src/util/inner.rs"
            ]
        );
    }

    #[test]
    fn scans_the_rust_files_of_the_package_outside_src() {
        let denied = "pub type Map = HashMap<u8, u8>;\n";
        let report = check(&tree(&[
            (
                "src/lib.rs",
                "#[path = \"../extra/outside.rs\"]\nmod outside;\n",
            ),
            ("extra/outside.rs", denied),
            (
                "build.rs",
                "fn main() {\n    let _ = HashSet::<u8>::new();\n}\n",
            ),
            ("xtask/src/main.rs", denied),
            ("checks/allocation/src/main.rs", denied),
            ("tests/integration.rs", denied),
            ("benches/speed.rs", denied),
            ("examples/demo.rs", denied),
            ("src/notes.txt", denied),
        ]));
        assert_eq!(
            report.problems,
            [
                "build.rs:2: `HashSet` is not allowed in non-test code",
                "extra/outside.rs:1: `HashMap` is not allowed in non-test code",
            ]
        );
        assert_eq!(
            report.files,
            ["build.rs", "extra/outside.rs", "src/lib.rs", "src/main.rs"]
        );
    }

    // Only the listed check crate is exempt from the source scan: another
    // file under `checks/`, such as one that library code includes with
    // `#[path]`, is scanned, and a crate under `checks/` that is not listed
    // is a finding, since its lock file would not be checked.
    #[test]
    fn files_under_checks_outside_the_check_crate_are_scanned() {
        let report = check(&tree(&[
            (
                "src/lib.rs",
                "#[path = \"../checks/shared/inner.rs\"]\nmod inner;\n",
            ),
            (
                "checks/shared/inner.rs",
                "pub type Map = HashMap<u8, u8>;\n",
            ),
            ("checks/other/Cargo.toml", CHECK_MANIFEST),
            ("checks/other/Cargo.lock", CHECK_LOCK),
            (
                "checks/allocation/src/main.rs",
                "pub type Map = HashMap<u8, u8>;\n",
            ),
        ]));
        assert_eq!(
            report.problems,
            [
                "checks/other/Cargo.lock: a crate under checks/ that is not a listed check crate",
                "checks/other/Cargo.toml: a crate under checks/ that is not a listed check crate",
                "checks/shared/inner.rs:1: `HashMap` is not allowed in non-test code",
            ]
        );
        assert_eq!(
            report.files,
            ["checks/shared/inner.rs", "src/lib.rs", "src/main.rs"]
        );
    }

    #[test]
    fn a_rust_file_that_cannot_be_scanned_is_a_finding() {
        let mut tree = tree(&[]);
        tree.insert("src/link.rs", Entry::Symlink);
        tree.insert("src/vendor.rs", Entry::Submodule);
        tree.insert("src/latin1.rs", Entry::File(vec![b'/', b'/', 0xe9, b'\n']));
        tree.insert("tests/link.rs", Entry::Symlink);
        let report = check(&tree);
        assert_eq!(
            report.problems,
            [
                "src/latin1.rs: a symbolic link, a submodule or not UTF-8, so the guard cannot scan it",
                "src/link.rs: a symbolic link, a submodule or not UTF-8, so the guard cannot scan it",
                "src/vendor.rs: a symbolic link, a submodule or not UTF-8, so the guard cannot scan it",
            ]
        );
        assert_eq!(report.files, ["src/lib.rs", "src/main.rs"]);
    }

    #[test]
    fn the_step_records_what_it_read_whether_it_passes_or_fails() {
        let mut facts = Facts::new();
        let _ = run(&repo::root(), &mut facts);
        let keys: Vec<&str> = facts.iter().map(|(key, _)| key.as_str()).collect();
        assert_eq!(keys, ["files", "std_paths", "crates"]);
        assert!(facts[0].1.contains("src/lib.rs"), "{facts:?}");
    }

    #[test]
    fn the_lists_of_the_repository_are_valid() {
        let root = repo::root();
        let mut problems = Vec::new();
        let std = std_entries(
            &fs::read_to_string(root.join(STD_PATHS)).unwrap(),
            &mut problems,
        );
        let crates = crate_entries(
            &fs::read_to_string(root.join(CRATES)).unwrap(),
            &mut problems,
        );
        assert_eq!(problems, Vec::<String>::new());
        assert!(!std.is_empty() && !crates.is_empty());
        assert!(crates.iter().all(|name| !denied_crate(name)));
    }
}
