# Contributing

kalyx is built from its foundations in this repository. The Rust package
`kalyx` at the repository root holds the library and the command-line
program. The Rust workspace `xtask/` holds the repository checks, with the
`xtask` alias in `.cargo/config.toml`, `rust-toolchain.toml` and the CI
workflow `.github/workflows/check.yml`. These are the commands that apply
today, run from the repository root:

```sh
git config --local core.hooksPath .githooks
rustup toolchain install
cargo build --locked
cargo test --locked
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo xtask check
git diff --check
git diff --cached --check
```

The first command enables the commit message hook in `.githooks/commit-msg`.
The second installs the Rust toolchain that `rust-toolchain.toml` pins. The
next four build, test, format-check and lint the library, and
`cargo xtask check` runs the [checks](#checks), which do not cover the library
package yet. The last two report whitespace errors in unstaged and
staged changes.

## Library rules

[AGENTS](AGENTS.md) lists the rules that library code follows: interfaces,
panics and dependencies, the porting record, and documentation.

## Porting record

Code taken over from the earlier implementation of the casξ computer algebra
system, which is not public, is recorded in [PORTING.md](PORTING.md): one row
per module, added in the same change as the code. The record states where the
code came from, what changed and which tests were not carried over.

## Checks

`cargo xtask check` runs these steps in order and stops at the first one that
fails:

1. `fmt`, `clippy` with warnings as errors, and `test`, in the `xtask`
   workspace;
2. `docs`: every relative link, image source and anchor in a Markdown file
   resolves to a tracked file or directory and, in a Markdown file, to a
   heading;
3. `commits`: every commit from the base to `HEAD` has a header that
   `.githooks/commit-msg` accepts. The base is the revision that the
   environment variable `CHECK_BASE` names; when it is unset, empty or all
   zeros, the base is the merge base of `origin/main` and `HEAD`;
4. `workflows`: every `.yml` or `.yaml` file below `.github/workflows/` is
   UTF-8 and one YAML document without anchors, aliases, merge keys, repeated
   keys or characters that YAML parsers read differently, and never mentions
   `pull_request_target` in any letter case, not even in a comment or
   through an escape; every job sets its own `permissions`; and in a
   workflow that runs on `pull_request`, or whose `on` is missing, empty or
   unreadable, no job requests write access or references `secrets`.

The `docs` and `workflows` steps read only files that Git tracks, so build
output and ignored files do not change the result; add a new file to the index
with `git add` before running the check.

`cargo xtask check --receipt <path>` also writes a JSON receipt of the run to
`<path>`, whether the check passes or fails. It records the commit, whether
the working tree was clean before and after the run, the `rustc` version, each
step with its status, duration and what it read (such as the base and the
number of commits that the commits step checked), the runner image
(`ImageOS`, `ImageVersion`) and the GitHub Actions run (`GITHUB_RUN_ID`,
`GITHUB_RUN_ATTEMPT`, `GITHUB_EVENT_NAME`, `GITHUB_REF`, `GITHUB_SHA`); a
value the environment does not provide is `null`.

CI runs the check as the job `cargo xtask check` of
`.github/workflows/check.yml` on a GitHub-hosted `ubuntu-24.04-arm` runner,
for the head commit of every pull request to `main` and for every push to
`main`. It sets `CHECK_BASE` to the base commit of the pull request or to the
previous head of `main`, and uploads the receipt as the artifact
`check-receipt-<commit>-<attempt>`.

## Commit messages

Commit messages use English Conventional Commits with a header of at most 72
characters, for example `docs(readme): describe the build`. The accepted types
are `feat`, `fix`, `docs`, `style`, `refactor`, `perf`, `test`, `build`, `ci`,
`chore` and `revert`. Headers that start with `Merge `, `Revert `, `fixup! `
or `squash! ` are accepted as they are. Do not bypass the hook or change
global Git configuration.

## Documentation

Documentation is English and written for a person who uses or builds on the
library. It presents as available only what the library ships today, marks
plans as plans and shows only commands that run from this repository. Code
comments are English too, and mathematics is written as LaTeX. Milestone,
task, proposal and decision numbers, stage codes, agent narratives, review
histories and evidence ledgers belong in the project's coordination records
outside this repository and appear in no document here.

## License

kalyx is released under the [MIT License](LICENSE). The copyright holders are
the casξ Authors, listed in [AUTHORS](AUTHORS). Contributions are accepted
under the same license.
