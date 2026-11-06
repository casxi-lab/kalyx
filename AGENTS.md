# Repository instructions

- kalyx is the computer algebra library of casξ. Until its code moves here,
  the library is developed in a separate repository that is not public, and
  this repository holds only the skeleton: `README.md`, `AGENTS.md`,
  `CONTRIBUTING.md`, `LICENSE`, `AUTHORS`, `.gitignore`,
  `.githooks/commit-msg`, the logo files in `.github/assets/` and the
  repository checks.
- The repository checks are the Rust workspace `xtask/` with its
  `Cargo.lock`, the `xtask` alias in `.cargo/config.toml`,
  `rust-toolchain.toml` and the workflow `.github/workflows/check.yml` that
  runs them in CI. They check this repository and contain no library code.
- Make no other code changes here before the move. Do not add library code:
  source files, tests, fixtures, benchmarks, proofs, registries, feature
  documents, domain pages or another Cargo package. Changes to the library
  are made in its development repository, under its own rules.
- Do not copy library files into this repository. The move brings the library
  here with its complete Git history. It is a separate, authorized change, and
  that change also replaces these instructions with the rules for the library.
- Changes allowed before the move are corrections to the skeleton files,
  including the repository checks. Describe only capabilities that the
  library ships today, and show no command that cannot be run from this
  repository.
- Write all documentation in English, for a person who uses or builds on the
  library: what it does, how to run it, its limits, and commands that actually
  run. Call the device casξ; use `casxi` where only ASCII is allowed, such as
  identifiers and paths.
- Keep milestone, task, proposal and decision numbers, stage codes, agent
  narratives, review histories and evidence ledgers in the project's
  coordination records outside this repository. They appear in no document
  here.
- Use English Conventional Commit subjects of at most 72 characters and the
  local `.githooks/commit-msg` hook; the check applies the same header rules
  to every commit of a change. Preserve history. Do not change global Git
  configuration, create remotes, tags or releases, or publish without
  authorization.
- Write the repository checks in Rust 2024, formatted with rustfmt and free
  of Clippy warnings, with unit tests in `#[cfg(test)]` modules next to the
  code. A change to a check adds tests for the cases it rejects.
- Before committing, run `cargo xtask check` from the repository root; it
  must pass. [CONTRIBUTING](CONTRIBUTING.md#checks) describes its steps. Also
  run `git diff --check` and `git diff --cached --check` and review the
  staged diff.
