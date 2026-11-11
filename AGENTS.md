# Repository instructions

- kalyx is the computer algebra library of casξ: the Rust package `kalyx` at
  the repository root, with a library and a command-line program, built from
  its foundations. The Rust workspace `xtask/` holds the repository checks,
  which CI runs as `cargo xtask check`; one of them, the allocation check in
  `checks/allocation/`, is a workspace of its own whose counting allocator is
  the only `unsafe` code that the checks build. The file
  `xtask/src/formal/process.rs` of the proof tooling, which no module declares
  yet, calls libc in `unsafe` blocks.
- The library is an ordinary Rust `std` library for 64-bit targets. Keep exact
  values exact. Pass a request-local context through parsing and computation,
  and check limits, the deadline and cancellation before potentially expensive
  work; these checks are cooperative.
- Library code follows these rules. `unsafe` code is forbidden, and
  floating-point arithmetic is denied until the machine floating-point path is
  added; the release profile keeps overflow checks. Non-test code uses no
  threads, hash containers, `RandomState`, `SystemTime`, `thread_local!`,
  `catch_unwind`, `static mut` or the transcendental functions of the platform
  math library, and constructs the context only in the command entry and the
  program. Non-test code makes no explicit panic (`unwrap`, `expect`,
  `panic!`, `unreachable!`, `todo!`, `unimplemented!`), and every `#[allow]`
  states its reason. Non-test code uses only the `std` paths listed in
  [guard/std-paths.txt](guard/std-paths.txt). The library's only direct
  third-party dependencies are num-bigint, num-rational and num-traits, which
  the `number` module wraps; `Cargo.lock` may hold only the packages listed in
  [guard/crates.txt](guard/crates.txt), and adding a dependency is a reviewed
  change of its own. `cargo xtask check` enforces these rules, within the
  limits that [CONTRIBUTING](CONTRIBUTING.md#guard) states: the compiler and
  Clippy check the attributes and lints in `Cargo.toml`, `src/lib.rs` and
  `clippy.toml`, and the guard step checks the rest, including the release
  profile and the license. Extending either list is a reviewed change of its
  own.
- Public interfaces follow the
  [public API conventions](docs/conventions/public-api.md). Components follow
  the tiers and design rules of the [architecture](docs/architecture.md);
  a change to a component's tier, first caller or foundation rule updates
  that document in the same change.
- Code that is to become a proof target is written in the subset of Rust that
  Charon and Aeneas translate into Lean 4. The subset, the proof workflow and
  the register of proof targets are added with the first proof target.
- Code taken over from the earlier implementation of the casξ computer algebra
  system is ported module by module, never copied wholesale. Each port adds a
  row to [PORTING.md](PORTING.md) in the same change, with its source written
  as `cas-project@<full commit SHA>:<path>`, where `cas-project` names the
  earlier implementation. A known deviation of the source is either corrected,
  with a test that rejects it, or recorded as a limitation; it is never
  carried over silently. Ported code is tested again here: tests, proofs and
  results of the earlier implementation are not evidence for kalyx.
- The proof tooling is taken over from krepi at a fixed commit, file by
  file, either byte for byte or with only the names of kalyx, except for the
  parts that kalyx needs of its own; each file is recorded in
  [PORTING.md](PORTING.md) in the same change, with its source written as
  `krepi@<full commit SHA>:<path>`. Third-party files of the tooling keep
  their own license.
- Write all documentation and code comments in English, for a person who uses
  or builds on the library: what it does, how to run it, its limits, and
  commands that actually run. Present as available only what the library ships
  today, and mark plans as plans. Call the device casξ; use `casxi` where only
  ASCII is allowed, such as identifiers and paths. Write mathematics in
  Markdown as LaTeX: `$...$` inline and `math` fenced blocks for display.
- Requirement identifiers that label requirements within a component may
  appear in documents and code. Milestone, task, proposal and decision
  numbers, stage codes, agent narratives, review histories and evidence
  ledgers are kept in the project's coordination records outside this
  repository and appear in no document here.
- Use English Conventional Commit subjects of at most 72 characters and the
  local `.githooks/commit-msg` hook; the check applies the same header rules
  to every commit of a change. Preserve history. Do not change global Git
  configuration, create remotes, tags or releases, or publish without
  authorization.
- Write the library and the repository checks in Rust 2024, formatted with
  rustfmt and free of Clippy warnings, with unit tests in `#[cfg(test)]`
  modules next to the code. A change to a check adds tests for the cases it
  rejects.
- Before committing, run `cargo xtask check` from the repository root; it
  must pass. It format-checks, lints and tests both the package and the
  checks, and runs the guard; [CONTRIBUTING](CONTRIBUTING.md#checks)
  describes its steps. Also run `git diff --check` and
  `git diff --cached --check` and review the staged diff.
