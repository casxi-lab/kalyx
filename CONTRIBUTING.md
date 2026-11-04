# Contributing

kalyx does not accept code yet. The library is developed in a separate
repository that is not public, until its code and complete history move into
this repository.

Changes here are limited to the skeleton files: `README.md`, `AGENTS.md`,
`CONTRIBUTING.md`, `LICENSE`, `AUTHORS`, `.gitignore`, the logo files in
`.github/assets/` and the commit hook. There is no Cargo package, so there is
nothing to build or test. These are the commands that apply today:

```sh
git config --local core.hooksPath .githooks
git diff --check
git diff --cached --check
```

The first command enables the commit message hook in `.githooks/commit-msg`.
The other two report whitespace errors in unstaged and staged changes.

## Commit messages

Commit messages use English Conventional Commits with a header of at most 72
characters, for example `docs(readme): describe the planned move`. The
accepted types are `feat`, `fix`, `docs`, `style`, `refactor`, `perf`, `test`,
`build`, `ci`, `chore` and `revert`. Do not bypass the hook or change global
Git configuration.

## Documentation

Documentation is English and written for a person who uses or builds on the
library. It describes only what the library ships today and shows only
commands that run from this repository. Milestone, task, proposal and decision
numbers, agent narratives and evidence ledgers belong in the project's
coordination records outside this repository and appear in no document here.

## Private repositories

This repository is public. Documents, code comments and commit messages do not
name or link the project's private repositories. Refer to their content in
neutral terms (the library's development repository, the coordination
records) and give only commit hashes and paths where a reference must be
traceable. The documentation check rejects lines that match the
case-insensitive pattern `casxi-(system|cas|build)|krepi-h[i]l|erthoaers[/]`.

## License

kalyx is released under the [MIT License](LICENSE). The copyright holders are
the casξ Authors, listed in [AUTHORS](AUTHORS). Contributions are accepted
under the same license.
