# Contributing

kalyx is built from its foundations in this repository. The Rust package
`kalyx` at the repository root holds the library and the command-line
program. The Rust workspace `xtask/` holds the repository checks, with the
`xtask` alias in `.cargo/config.toml`, `rust-toolchain.toml`, the allow lists
of the guard in `guard/` and the CI workflow `.github/workflows/check.yml`;
the package `checks/allocation/`, a workspace of its own, holds the
[allocation check](#allocation-check) that the checks run.
These are the commands that apply today, run from the repository root:

```sh
git config --local core.hooksPath .githooks
rustup toolchain install
cargo build --locked
cargo xtask check
git diff --check
git diff --cached --check
```

The first command enables the commit message hook in `.githooks/commit-msg`.
The second installs the Rust toolchain that `rust-toolchain.toml` pins. The
third builds the library and the program, and `cargo xtask check` runs the
[checks](#checks), which format-check, lint and test both the package and the
checks and run the guard. The last two report whitespace errors in unstaged
and staged changes.

## Library rules

[AGENTS](AGENTS.md) lists the rules that library code follows: interfaces,
panics and dependencies, the porting record, and documentation. Public
interfaces follow the
[public API conventions](docs/conventions/public-api.md), and components
follow the verification tiers and the foundation design rules of the
[architecture](docs/architecture.md). The
`kalyx-clippy` and `guard` steps of the [checks](#checks) enforce the rules
for code, dependencies, the release profile and the license, within the
limits that the [guard](#guard) section states.

## Porting record

Code taken over from the earlier implementation of the casξ computer algebra
system, which is not public, and the proof tooling taken over from krepi are
recorded in [PORTING.md](PORTING.md): one row per module or file, added in the
same change as the code. The record states where the code came from, what
changed and which tests were not carried over.

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
   unreadable, no job requests write access or references `secrets`;
5. `kalyx-fmt`, `kalyx-clippy` with warnings as errors, and `kalyx-test`
   (`cargo test --locked`), on the kalyx package at the repository root.
   For every target of the package, `Cargo.toml` forbids `unsafe` code and
   denies floating-point arithmetic, `unwrap`, `expect`, `panic!`,
   `unreachable!`, `todo!`, `unimplemented!` and an `#[allow]` without a
   `reason`; `clippy.toml` allows `unwrap`, `expect` and `panic!` in tests,
   and disallows the transcendental functions of the platform math library
   (listed [below](#guard)) as methods of `f32` and `f64` and of the `Float`
   and `Real` traits of num-traits. Clippy resolves the type, so a call
   through a type alias or a generic parameter is caught too; this applies
   to tests as well;
6. `kalyx-allocation`: `cargo fmt --all --check`, `cargo clippy
   --all-targets --locked` with warnings as errors, `cargo test --locked`,
   which tests the verdict of the check on the runs that it rejects, and
   `cargo run --locked` on the [allocation check](#allocation-check) in
   `checks/allocation/`;
7. `guard`: the rules of the package that the compiler and Clippy do not
   check, described [below](#guard).

The `docs`, `workflows` and `guard` steps read only files that Git tracks, so
build output and ignored files do not change the result; add a new file to the
index with `git add` before running the check.

### Allocation check

The allocation check runs each of the 58 cases of
[the answer vectors](vectors/README.md) 100 times through the command entry,
under the limits of the case and under a counting global allocator, and fails
unless every run leaves the live bytes of the process at their baseline, as
the
[contract of the command entry](docs/components/command/contract.md#the-allocation-check)
states. A global allocator implements the unsafe trait `GlobalAlloc`, and
the kalyx package forbids `unsafe` code in every target, so the check is the
package `checks/allocation/`, a workspace of its own outside the package that
depends on it by path, like `xtask/`. Its allocator wrapper is the only
`unsafe` code that the checks build (the files of the proof tooling in
`xtask/src/formal/`, which no module declares yet, call libc in `unsafe`
blocks): the manifest of the check denies `unsafe`
code and undocumented unsafe blocks, and only the wrapper allows `unsafe`
code, with its reason, and states why each unsafe block is sound. The guard
does not scan the check, which is not code of the package, and checks its
lock file as [below](#guard).

The same program measures the [resource profile](docs/resource-profile.md)
of the library, the heap and the stack of each case and of deep inputs, when
it is run by hand with
`cargo run --locked --release --manifest-path checks/allocation/Cargo.toml -- profile`;
`cargo xtask check` does not run the profile.

### Guard

The guard reads every tracked `.rs` file outside `xtask/`,
`checks/allocation/`, `verification/`, `tests/`, `benches/` and `examples/`,
such as the files
below `src/`, a build script and any other file under `checks/`; such a file that is a symbolic link, a submodule or not UTF-8
is a finding. It skips test code: an item, module, associated item, `let`
statement or macro statement marked `#[test]` or with a `#[cfg(...)]` that
holds only in test builds, such as `#[cfg(test)]`, and the file of a module
that only test code declares, as `#[cfg(test)] mod name;`, with the files of
its submodules. A `#[cfg(test)]` on an expression, field, variant or match
arm does not exempt it, and a file that scanned code also declares as
`mod name;` is scanned. The files are parsed as Rust, so comments and string
literals never count; the bodies of macros are read token by token. The step
fails, listing every finding with its file and line, when non-test code
holds:

- `std::thread` or a path below it; the identifiers `HashMap`, `HashSet`,
  `RandomState`, `SystemTime`, `thread_local` and `catch_unwind` wherever
  they appear, including names that the package defines; or a `static mut`
  item;
- a call `.name(` or a path `f32::name` or `f64::name`, where `name` is a
  transcendental function of the platform math library: `sin`, `cos`, `tan`,
  `sin_cos`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`, `tanh`,
  `asinh`, `acosh`, `atanh`, `exp`, `exp2`, `exp_m1`, `ln`, `log`, `log2`,
  `log10`, `ln_1p`, `powf`, `cbrt` or `hypot`. The guard matches names, so
  `.log(` on any value counts; a call through a type alias, a generic
  parameter or a trait is left to Clippy, as step 5 describes;
- outside `src/main.rs`, `src/command.rs` and `src/command/`, a path
  `Context::name` or `<Context as Trait>::name` with any `name`, so every
  associated function counts as constructing the context; a struct
  expression `Context { .. }`; an import that renames `Context`; or a type
  alias of `Context`. Inside the impl blocks of the context type, its
  constructors build the value as `Self`. The guard does not see a value
  built as `Self`, through an inferred `Default::default()` or through a
  conversion such as `From`; review keeps those to the command entry and
  the program;
- a path that starts with `std` and that
  [guard/std-paths.txt](guard/std-paths.txt) does not permit.

An entry of `guard/std-paths.txt` is a `std` path of at least two segments
and permits that path and every path below it: `std::fmt` permits
`std::fmt::Display`, and `std::io::Write` permits `std::io::Write::flush` but
not `std::io::WriteFmt`. The guard checks the paths in `use` declarations,
expressions, types, patterns, macros and attributes, and expands `use` trees
first: `use std::{fmt, io::Write};` names `std::fmt` and `std::io::Write`,
and a glob `use std::fmt::*;` names `std::fmt`. Importing a module, as in
`use std::io;`, therefore needs the module itself in the list. The list holds
the process interface of the program (arguments, standard streams, the exit
code and `std::time::Instant`) and the std re-exports of basic types and
traits of core and alloc. It never holds, and the guard rejects an entry that
would permit, `std::thread`, `std::thread_local`, `HashMap`, `HashSet`, the
rest of `hash_map` and `hash_set`, `RandomState`, `SystemTime`,
`UNIX_EPOCH` or `catch_unwind`.

`Cargo.lock` may hold only the package itself and the packages named in
[guard/crates.txt](guard/crates.txt), one name per line: today the `num-*`
packages for arbitrary-precision integers and rationals, which the `number`
module uses, and their build dependency `autocfg`. The lock file of the
allocation check, `checks/allocation/Cargo.lock`, may hold only the same
packages, the package itself and the check crate, and a `Cargo.toml` or
`Cargo.lock` elsewhere under `checks/` is a finding. `getrandom` and the
`rand`, `rayon` and `crossbeam` families (`rand_core`, `crossbeam-utils` and
the like) are rejected even if listed. The `license` field of the package in
`Cargo.toml` must be exactly `MIT`, and its `[profile.release]` table must
set `overflow-checks = true`. Extending either list is a reviewed change of
its own.

`cargo xtask check --receipt <path>` also writes a JSON receipt of the run to
`<path>`, whether the check passes or fails. It records the commit, whether
the working tree was clean before and after the run, the `rustc` version, each
step with its status, duration and what it read (such as the base and the
number of commits that the commits step checked, or the source files that the
guard read and the number of entries in each allow list), the runner image
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
under the same license. Third-party files keep their own license: the patch
of Aeneas in `verification/tooling/` is under the
[Apache License 2.0](verification/tooling/LICENSE-Apache-2.0).
