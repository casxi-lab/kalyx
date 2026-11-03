# Repository instructions

- kalyx is the computer algebra library of casξ. Until its code moves here,
  the library lives in erthoaers/casxi-cas, and this repository holds only the
  skeleton: `README.md`, `AGENTS.md`, `CONTRIBUTING.md`, `.gitignore`,
  `.githooks/commit-msg` and the logo files in `.github/assets/`.
- Make no code changes here before the move. Do not add source files, tests,
  fixtures, benchmarks, proofs, registries, feature documents, domain pages or
  a Cargo package. Make every change to the library in casxi-cas, following the
  `AGENTS.md` and `CONTRIBUTING.md` of casxi-cas.
- Do not copy files from casxi-cas into this repository. The move brings
  casxi-cas here with its complete Git history. It is a separate, authorized
  change, and that change also replaces these instructions with the rules for
  the library.
- Changes allowed before the move are corrections to the skeleton files. Keep
  them consistent with casxi-cas: describe only capabilities that casxi-cas
  ships, mark them as running from casxi-cas, and run every command shown in
  `README.md` in a casxi-cas checkout before stating its output.
- Write all documentation in English, for a person who uses or builds on the
  library: what it does, how to run it, its limits, and commands that actually
  run. Call the device casξ; use `casxi` where only ASCII is allowed, such as
  identifiers and paths.
- Keep milestone, task, proposal and decision numbers, stage codes, agent
  narratives, review histories and evidence ledgers in `casxi-build`. They
  appear in no document here.
- Use English Conventional Commit subjects of at most 72 characters and the
  local `.githooks/commit-msg` hook. Preserve history. Do not change global Git
  configuration, create remotes, tags or releases, or publish without
  authorization.
- There is no build or test command here. Before committing, run
  `git diff --check` and `git diff --cached --check` and review the staged
  diff.
