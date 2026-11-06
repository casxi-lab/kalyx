//! The commits step: every commit that a change adds has a message header
//! that the commit-msg hook in `.githooks/commit-msg` accepts.
//!
//! # Range
//!
//! The step checks the commits in `<base>..HEAD`. The base is the revision
//! that the environment variable [`BASE_VAR`] names. When the variable is
//! unset, empty or all zeros, as `github.event.before` is on a push that
//! creates a branch, the base is the merge base of [`UPSTREAM`] and `HEAD`.
//!
//! # Rules
//!
//! The rules are those of the hook. The header is the first line of the
//! message that neither starts with `#` nor holds only white space. A header
//! that starts with `Merge `, `Revert `, `fixup! ` or `squash! ` passes.
//! Any other header has the form `<type>[(scope)][!]: <description>`, where
//! the type is one of [`TYPES`], the scope is one or more of `a-z`, `0-9`,
//! `.`, `_`, `/` and `-`, and the description starts with a character that
//! is not white space; and it is at most [`MAX_HEADER`] characters long.

use std::path::Path;
use std::process::Command;

use crate::check::Facts;

/// The environment variable that names the base commit.
pub const BASE_VAR: &str = "CHECK_BASE";

/// The branch whose merge base with `HEAD` is the base when [`BASE_VAR`]
/// names none.
pub const UPSTREAM: &str = "origin/main";

/// The commit types that a header may use.
pub const TYPES: [&str; 11] = [
    "feat", "fix", "docs", "style", "refactor", "perf", "test", "build", "ci", "chore", "revert",
];

/// The longest header, in characters.
pub const MAX_HEADER: usize = 72;

/// Header prefixes that pass without further checks.
const EXEMPT: [&str; 4] = ["Merge ", "Revert ", "fixup! ", "squash! "];

/// The commits step, with the base taken from [`BASE_VAR`].
pub fn run(root: &Path, facts: &mut Facts) -> Result<(), String> {
    let variable = std::env::var(BASE_VAR).ok();
    check_range(root, variable.as_deref(), facts)
}

/// Checks the commits in `<base>..HEAD` of the repository at `root`, where
/// `variable` is the value of [`BASE_VAR`]. The base, where it came from
/// and the number of commits checked become facts.
fn check_range(root: &Path, variable: Option<&str>, facts: &mut Facts) -> Result<(), String> {
    let base = match given_base(variable)? {
        Some(revision) => {
            facts.push(("base_from".to_string(), BASE_VAR.to_string()));
            git(
                root,
                &["rev-parse", "--verify", &format!("{revision}^{{commit}}")],
            )
            .map_err(|error| format!("{BASE_VAR}={revision} does not name a commit: {error}"))?
        }
        None => {
            facts.push((
                "base_from".to_string(),
                format!("merge base of {UPSTREAM} and HEAD"),
            ));
            git(root, &["merge-base", UPSTREAM, "HEAD"]).map_err(|error| {
                format!("cannot find the merge base of {UPSTREAM} and HEAD; fetch {UPSTREAM} or set {BASE_VAR}: {error}")
            })?
        }
    };
    let base = String::from_utf8_lossy(&base).trim().to_string();
    facts.push(("base".to_string(), base.clone()));
    let log = git(
        root,
        &["log", "-z", "--format=%H%n%B", &format!("{base}..HEAD")],
    )?;
    let commits = parse_log(&log)?;
    facts.push(("commits".to_string(), commits.len().to_string()));
    println!("commits: {} in {base}..HEAD", commits.len());
    let problems = problems(&commits);
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// The base revision that the value of [`BASE_VAR`] names, or `None` when
/// the merge base is to be used instead. A value that starts with `-` would
/// be read as an option and is rejected.
pub fn given_base(value: Option<&str>) -> Result<Option<&str>, String> {
    let Some(value) = value.map(str::trim).filter(|value| !value.is_empty()) else {
        return Ok(None);
    };
    if value.chars().all(|c| c == '0') {
        return Ok(None);
    }
    if value.starts_with('-') {
        return Err(format!("{BASE_VAR}={value} is not a revision"));
    }
    Ok(Some(value))
}

/// The standard output of a successful Git command in `root`.
fn git(root: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    let shown = format!("git {}", args.join(" "));
    let output = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .map_err(|error| format!("cannot run `{shown}`: {error}"))?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(format!(
            "`{shown}` failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ))
    }
}

/// A commit in the range: its hash and its message, or `None` when the
/// message is not UTF-8.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Commit {
    pub hash: String,
    pub message: Option<String>,
}

/// Reads the output of `git log -z --format=%H%n%B`: one record per commit,
/// ended by a NUL byte, that holds the hash, a line break and the message.
pub fn parse_log(output: &[u8]) -> Result<Vec<Commit>, String> {
    let mut commits = Vec::new();
    for record in output.split(|&byte| byte == 0) {
        if record.is_empty() {
            continue;
        }
        let (hash, message) = match record.iter().position(|&byte| byte == b'\n') {
            Some(at) => (&record[..at], &record[at + 1..]),
            None => (record, &[][..]),
        };
        let hash = std::str::from_utf8(hash)
            .ok()
            .filter(|hash| !hash.is_empty() && hash.chars().all(|c| c.is_ascii_hexdigit()))
            .ok_or_else(|| {
                format!(
                    "unexpected git log record `{}`",
                    String::from_utf8_lossy(record)
                )
            })?;
        commits.push(Commit {
            hash: hash.to_string(),
            message: String::from_utf8(message.to_vec()).ok(),
        });
    }
    Ok(commits)
}

/// The problems of `commits`, each starting with the commit hash.
pub fn problems(commits: &[Commit]) -> Vec<String> {
    commits
        .iter()
        .filter_map(|commit| {
            let problem = match &commit.message {
                Some(message) => header_problem(message)?,
                None => "the message is not UTF-8".to_string(),
            };
            Some(format!("{}: {problem}", commit.hash))
        })
        .collect()
}

/// White space as the POSIX `[[:space:]]` class has it in ASCII.
fn is_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\u{b}' | '\u{c}' | '\r')
}

/// The header of a commit message as the hook reads it: the first line that
/// neither starts with `#` nor holds only white space; empty when there is
/// none.
pub fn header(message: &str) -> &str {
    message
        .split('\n')
        .find(|line| !line.starts_with('#') && !line.chars().all(is_space))
        .unwrap_or_default()
}

/// Why the hook would reject `message`, if it would.
pub fn header_problem(message: &str) -> Option<String> {
    let header = header(message);
    if EXEMPT.iter().any(|prefix| header.starts_with(prefix)) {
        return None;
    }
    if !conventional(header) {
        return Some(format!(
            "the header `{header}` does not follow Conventional Commits: expected \
             `<type>[(scope)][!]: <description>` with a type among {}",
            TYPES.join(", ")
        ));
    }
    let length = header.chars().count();
    if length > MAX_HEADER {
        return Some(format!(
            "the header `{header}` is {length} characters; keep it at most {MAX_HEADER}"
        ));
    }
    None
}

/// Whether `header` has the form `<type>[(scope)][!]: <description>`.
fn conventional(header: &str) -> bool {
    TYPES
        .iter()
        .filter_map(|kind| header.strip_prefix(kind))
        .any(after_type)
}

/// Whether `rest`, the header after its type, is `[(scope)][!]: ` followed
/// by a description that starts with a character that is not white space.
fn after_type(rest: &str) -> bool {
    let rest = match rest.strip_prefix('(') {
        Some(scoped) => {
            let Some(end) = scoped.find(')') else {
                return false;
            };
            let scope = &scoped[..end];
            let scope_char = |c: char| {
                c.is_ascii_lowercase() || c.is_ascii_digit() || matches!(c, '.' | '_' | '/' | '-')
            };
            if scope.is_empty() || !scope.chars().all(scope_char) {
                return false;
            }
            &scoped[end + 1..]
        }
        None => rest,
    };
    let rest = rest.strip_prefix('!').unwrap_or(rest);
    rest.strip_prefix(": ")
        .and_then(|description| description.chars().next())
        .is_some_and(|first| !is_space(first))
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::io::Write;
    use std::path::PathBuf;
    use std::process::Stdio;

    use super::*;

    fn accepted(message: &str) -> bool {
        header_problem(message).is_none()
    }

    #[test]
    fn accepts_conventional_headers() {
        for message in [
            "docs(readme): describe the planned move",
            "ci: add the check workflow\n\nThe body is not checked.\n",
            "feat(api)!: change the evaluation result contract",
            "fix!: drop a field",
            "test(a.b/c_d-1): cover a scope with every allowed character",
            "revert: undo the last change",
            "chore: x",
        ] {
            assert!(accepted(message), "{message}");
        }
        for kind in TYPES {
            assert!(accepted(&format!("{kind}: describe it")), "{kind}");
        }
    }

    #[test]
    fn the_header_is_the_first_line_that_is_not_a_comment_or_blank() {
        let message = "# Please enter the commit message\n\n \t\u{b}\ndocs: x\n# trailing\n";
        assert_eq!(header(message), "docs: x");
        assert!(accepted(message));
        assert_eq!(header("#only\n\n  \n"), "");
        assert_eq!(header(""), "");
        assert_eq!(header("  docs: indented"), "  docs: indented");
    }

    #[test]
    fn exempt_prefixes_pass() {
        let long_merge =
            "Merge pull request #12 from casxi-lab/ci/check-workflow-with-a-long-branch-name";
        assert!(long_merge.chars().count() > MAX_HEADER);
        for message in [
            long_merge,
            "Merge branch 'main'",
            "Revert \"docs: x\"",
            "fixup! docs: x",
            "squash! anything at all",
        ] {
            assert!(accepted(message), "{message}");
        }
    }

    #[test]
    fn rejects_headers_that_do_not_follow_conventional_commits() {
        for message in [
            "",
            "# only a comment\n\n",
            "Docs: capital type",
            "feature: unknown type",
            "docs:no space",
            "docs: ",
            "docs:  starts with a space",
            "docs: \tstarts with a tab",
            "docs(Readme): capital scope",
            "docs(): empty scope",
            "docs(readme: unclosed scope",
            "docs(read me): space in the scope",
            "docs (readme): space before the scope",
            "docs!!: two marks",
            "docs!(readme): mark before the scope",
            "Merge",
            "merge branch 'main'",
            "fixup!docs: x",
            "  docs: indented",
        ] {
            let problem = header_problem(message);
            assert!(
                problem
                    .as_deref()
                    .is_some_and(|text| text.contains("does not follow Conventional Commits")),
                "{message:?}: {problem:?}"
            );
        }
    }

    #[test]
    fn rejects_a_header_longer_than_72_characters() {
        let at_limit = format!("docs: {}", "x".repeat(MAX_HEADER - 6));
        assert_eq!(at_limit.chars().count(), MAX_HEADER);
        assert!(accepted(&at_limit));
        let too_long = format!("{at_limit}y");
        let problem = header_problem(&too_long).expect("a problem");
        assert!(problem.contains("is 73 characters"), "{problem}");
        // Characters are counted, not bytes.
        let wide = format!("docs: {}", "ξ".repeat(MAX_HEADER - 6));
        assert!(wide.len() > MAX_HEADER);
        assert!(accepted(&wide));
    }

    #[test]
    fn the_base_comes_from_the_variable_unless_it_is_empty_or_zero() {
        assert_eq!(given_base(None), Ok(None));
        assert_eq!(given_base(Some("")), Ok(None));
        assert_eq!(given_base(Some(" \n")), Ok(None));
        assert_eq!(given_base(Some(&"0".repeat(40))), Ok(None));
        assert_eq!(given_base(Some(&"0".repeat(64))), Ok(None));
        assert_eq!(given_base(Some("4bdc6db\n")), Ok(Some("4bdc6db")));
        assert_eq!(given_base(Some("origin/main")), Ok(Some("origin/main")));
        assert!(given_base(Some("--all")).is_err());
    }

    #[test]
    fn reads_git_log_records() {
        let output = b"aa11\nMerge pull request #1 from casxi-lab/x\n\0bb22\ndocs: x\n\nBody.\n\0cc33\n\xff\n\0";
        let commits = parse_log(output).expect("valid records");
        assert_eq!(
            commits,
            [
                Commit {
                    hash: "aa11".to_string(),
                    message: Some("Merge pull request #1 from casxi-lab/x\n".to_string()),
                },
                Commit {
                    hash: "bb22".to_string(),
                    message: Some("docs: x\n\nBody.\n".to_string()),
                },
                Commit {
                    hash: "cc33".to_string(),
                    message: None,
                },
            ]
        );
        assert_eq!(parse_log(b""), Ok(Vec::new()));
        assert!(parse_log(b"not a hash\ndocs: x\n\0").is_err());
    }

    #[test]
    fn reports_each_rejected_commit_by_hash() {
        let commits = [
            Commit {
                hash: "aa11".to_string(),
                message: Some("docs: fine\n".to_string()),
            },
            Commit {
                hash: "bb22".to_string(),
                message: Some("Update README.md\n".to_string()),
            },
            Commit {
                hash: "cc33".to_string(),
                message: None,
            },
        ];
        let found = problems(&commits);
        assert_eq!(found.len(), 2, "{found:?}");
        assert!(
            found[0].starts_with("bb22: the header `Update README.md` does not follow"),
            "{found:?}"
        );
        assert_eq!(found[1], "cc33: the message is not UTF-8");
    }

    /// A Git repository in the ignored build directory of this crate, with
    /// Git configuration from outside the repository turned off. It is
    /// removed when dropped.
    struct Scratch {
        dir: PathBuf,
    }

    impl Scratch {
        fn new(name: &str) -> Scratch {
            let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("target")
                .join(format!("commits-test-{name}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir).expect("create the scratch directory");
            let scratch = Scratch { dir };
            scratch.git(&["init", "--quiet"], "");
            scratch
        }

        /// Runs git with `input` on its standard input and returns its
        /// trimmed standard output.
        fn git(&self, args: &[&str], input: &str) -> String {
            let mut child = Command::new("git")
                .args(args)
                .current_dir(&self.dir)
                .env("GIT_CONFIG_GLOBAL", "/dev/null")
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .env("GIT_AUTHOR_NAME", "Test")
                .env("GIT_AUTHOR_EMAIL", "test@example.org")
                .env("GIT_COMMITTER_NAME", "Test")
                .env("GIT_COMMITTER_EMAIL", "test@example.org")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .expect("run git");
            let mut stdin = child.stdin.take().expect("the standard input");
            stdin.write_all(input.as_bytes()).expect("write to git");
            drop(stdin);
            let output = child.wait_with_output().expect("wait for git");
            assert!(
                output.status.success(),
                "git {args:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            String::from_utf8(output.stdout)
                .expect("UTF-8 output")
                .trim()
                .to_string()
        }

        /// Adds a commit with `message` and `parents` and moves the current
        /// branch to it. Plumbing commands run no hook.
        fn commit(&self, parents: &[&str], message: &str) -> String {
            let tree = self.git(&["write-tree"], "");
            let mut args = vec!["commit-tree", "--no-gpg-sign", tree.as_str()];
            for parent in parents {
                args.extend(["-p", *parent]);
            }
            let id = self.git(&args, message);
            self.git(&["update-ref", "HEAD", &id], "");
            id
        }

        fn check(&self, variable: Option<&str>) -> (Result<(), String>, Facts) {
            let mut facts = Facts::new();
            let result = check_range(&self.dir, variable, &mut facts);
            (result, facts)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.dir);
        }
    }

    fn fact<'a>(facts: &'a Facts, key: &str) -> Option<&'a str> {
        facts
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value.as_str())
    }

    #[test]
    fn checks_the_commits_after_the_base_including_merged_ones() {
        let scratch = Scratch::new("range");
        let first = scratch.commit(&[], "docs: initialize the repository\n");
        scratch.git(&["update-ref", "refs/remotes/origin/main", &first], "");
        let good = scratch.commit(&[&first], "feat(xtask): add a step\n");
        let side = scratch.commit(&[&first], "Add a step without a type\n");
        let merge = scratch.commit(&[&good, &side], "Merge branch 'side'\n");
        let rejected = format!("{side}: the header `Add a step without a type` does not follow");

        // Without a base, or with an all-zero one, the range starts at the
        // merge base with origin/main, and the merged side commit fails.
        let zeros = "0".repeat(40);
        for variable in [None, Some(""), Some(zeros.as_str())] {
            let (result, facts) = scratch.check(variable);
            let detail = result.expect_err("the side commit fails");
            assert_eq!(detail.lines().count(), 1, "{detail}");
            assert!(detail.starts_with(&rejected), "{detail}");
            assert_eq!(fact(&facts, "base"), Some(first.as_str()));
            assert_eq!(
                fact(&facts, "base_from"),
                Some("merge base of origin/main and HEAD")
            );
            assert_eq!(fact(&facts, "commits"), Some("3"));
        }

        // A given base checks exactly the commits after it.
        let (result, facts) = scratch.check(Some(&good));
        let detail = result.expect_err("the side commit fails");
        assert!(detail.starts_with(&rejected), "{detail}");
        assert_eq!(fact(&facts, "base"), Some(good.as_str()));
        assert_eq!(fact(&facts, "base_from"), Some(BASE_VAR));
        assert_eq!(fact(&facts, "commits"), Some("2"));
        let (result, facts) = scratch.check(Some(&side));
        assert_eq!(result, Ok(()));
        assert_eq!(fact(&facts, "commits"), Some("2"));
        let (result, facts) = scratch.check(Some(&merge));
        assert_eq!(result, Ok(()));
        assert_eq!(fact(&facts, "commits"), Some("0"));
    }

    #[test]
    fn rejects_a_base_that_names_no_commit() {
        let scratch = Scratch::new("bad-base");
        scratch.commit(&[], "docs: initialize the repository\n");
        let (result, _) = scratch.check(Some("no-such-ref"));
        let detail = result.expect_err("no such commit");
        assert!(
            detail.starts_with("CHECK_BASE=no-such-ref does not name a commit"),
            "{detail}"
        );
        let (result, _) = scratch.check(Some("--all"));
        assert_eq!(
            result,
            Err("CHECK_BASE=--all is not a revision".to_string())
        );
        // Without origin/main there is no merge base either.
        let (result, facts) = scratch.check(None);
        let detail = result.expect_err("no merge base");
        assert!(
            detail.starts_with("cannot find the merge base of origin/main and HEAD"),
            "{detail}"
        );
        assert_eq!(fact(&facts, "base"), None);
    }
}
