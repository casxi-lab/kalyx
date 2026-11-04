# Repository instructions

- kalyx is the computer algebra library of casξ. Until its code moves here,
  the library is developed in a separate repository that is not public, and
  this repository holds only the skeleton: `README.md`, `AGENTS.md`,
  `CONTRIBUTING.md`, `LICENSE`, `AUTHORS`, `.gitignore`,
  `.githooks/commit-msg` and the logo files in `.github/assets/`.
- Make no code changes here before the move. Do not add source files, tests,
  fixtures, benchmarks, proofs, registries, feature documents, domain pages or
  a Cargo package. Changes to the library are made in its development
  repository, under its own rules.
- Do not copy library files into this repository. The move brings the library
  here with its complete Git history. It is a separate, authorized change, and
  that change also replaces these instructions with the rules for the library.
- Changes allowed before the move are corrections to the skeleton files.
  Describe only capabilities that the library ships today, and show no command
  that cannot be run from this repository.
- Write all documentation in English, for a person who uses or builds on the
  library: what it does, how to run it, its limits, and commands that actually
  run. Call the device casξ; use `casxi` where only ASCII is allowed, such as
  identifiers and paths.
- Keep milestone, task, proposal and decision numbers, stage codes, agent
  narratives, review histories and evidence ledgers in the project's
  coordination records outside this repository. They appear in no document
  here.
- This repository is public: never name or link the project's private
  repositories; see [contributing](CONTRIBUTING.md#private-repositories).
- Use English Conventional Commit subjects of at most 72 characters and the
  local `.githooks/commit-msg` hook. Preserve history. Do not change global Git
  configuration, create remotes, tags or releases, or publish without
  authorization.
- There is no build or test command here. Before committing, run
  `git diff --check` and `git diff --cached --check` and review the staged
  diff.
