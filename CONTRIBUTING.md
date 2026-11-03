# Contributing

kalyx does not accept code yet. The library is developed in
[erthoaers/casxi-cas](https://github.com/erthoaers/casxi-cas) until its code
and complete history move into this repository. Send changes to the library
there, following the
[CONTRIBUTING](https://github.com/erthoaers/casxi-cas/blob/main/CONTRIBUTING.md)
and [AGENTS](https://github.com/erthoaers/casxi-cas/blob/main/AGENTS.md) files
of casxi-cas.

Changes here are limited to the skeleton files: `README.md`, `AGENTS.md`,
`CONTRIBUTING.md`, `.gitignore` and the commit hook. There is no Cargo package,
so there is nothing to build or test. These are the commands that apply today:

```sh
git config --local core.hooksPath .githooks
git diff --check
git diff --cached --check
```

The first command enables the commit message hook in `.githooks/commit-msg`.
The other two report whitespace errors in unstaged and staged changes.

## Commit messages

Commit messages use English Conventional Commits with a header of at most 72
characters, for example `docs(readme): describe the move from casxi-cas`. The
accepted types are `feat`, `fix`, `docs`, `style`, `refactor`, `perf`, `test`,
`build`, `ci`, `chore` and `revert`. Do not bypass the hook or change global
Git configuration.

## Documentation

Documentation is English and written for a person who uses or builds on the
library. It describes only what casxi-cas ships today, says that it runs from
casxi-cas, and shows only commands that run there. Milestone, task, proposal
and decision numbers, agent narratives and evidence ledgers belong in
`casxi-build` and appear in no document here.

## License

A license has not been selected yet.
