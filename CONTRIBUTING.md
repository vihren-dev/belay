# Contributing to Belay

This page says which contributions the project accepts and how to build the
repository. To use the library in a Lean project, read the [README](README.md).

## What the project accepts

For security reasons, the project does not accept pull requests that change
code. The team closes such a pull request and does not merge it. If you find a
defect or need a feature, open an issue.

The project accepts these contributions, each as an
[issue](https://github.com/vihren-dev/belay/issues):

- **A bug report or a request.** Say what you did, what you expected and what
  occurred.
- **A reproduction of a bug.** Give the smallest SQL that shows the bug, the
  output of the `sqlite3` shell for that SQL with the SQLite version, and the
  block that Belay printed. If Belay refuses the SQL or a Lean file does not
  compile, give the file and the error message.
- **A new test case.** Give SQL statements that the conformance evidence does
  not cover, and the output of the `sqlite3` shell. The team adds the case to
  the corpora, where each build replays it against native SQLite and against
  the model.

Ask questions in
[Discussions](https://github.com/vihren-dev/belay/discussions).

The sections that follow describe the build and the layout of the repository.
Use them to reproduce a bug or to read the code.

## Build the repository

Install Nix with `nix-command` and `flakes` enabled and a bootstrap Python 3,
then enter the development environment once for a batch:

```sh
python3 tools/check_resources.py
nix develop path:./nix
just test
```

Alternatively, install direnv and run `direnv allow`. Then `.envrc` loads
`shell.nix`, which has the same packages and also the pinned Lean toolchain for
local Lean builds; nix-direnv only caches it. The committed `nix/flake.lock`
fixes Nix dependencies for both shells. The small `nix/` directory is the
complete source of the flake shell; always use the explicit `path:` reference,
including from non-Git Jujutsu workspaces. See the
[resource and cleanup policy](team-guide.md#development-resources).
The resource check rejects less than 10 GiB free before expensive work. `just build`
builds the conformance runtime through Nix, including the exact official Lean release
in `lean-toolchain`. Initial dependency fetching needs network access; unchanged
builds reuse Nix outputs. No Elan or Mathlib is required.

The supported development systems are Apple Silicon macOS (`aarch64-darwin`)
and Intel/AMD Linux (`x86_64-linux`). Lean is pinned to 4.34.1; native SQLite is
built from the official 3.51.0 autoconf archive with its default configuration
and readline disabled. `nix build path:./nix#sqlite` builds that engine independently.
SQLite's compile settings can be inspected with `sqlite3 :memory: 'PRAGMA compile_options;'`.
These native checks are evidence, not a proof of correspondence with SQLite C.

## Test

`just build` builds the model, the conformance runner and the upstream-derived parser
library. `just test` builds prerequisites, reuses independently cached Nix test targets,
and runs the remaining source tests through pytest. Its conformance tier replays
all authored and synthetic cases plus a stable upstream sample.
`just test-full` also runs the complete model suite; CI uses it. `just test-nix` checks
the Nix build infrastructure. `just verdict` grades the development claims as the
verdict job does. Commands run under explicit timeouts and are also the entry points
for CI; see [CI](docs/ci.md) and [conformance coverage](docs/coverage.md).

Pytest also records test names, outcomes and durations automatically. See
[test observations](docs/test-observability.md) for local upload configuration,
retained reports and CI setup.

## Where things are

- **The model**, `packages/belay-sqlite-model` (`Belay.Sqlite.Model`): SQLite's statement
  syntax, its resolution against a catalog and the execution semantics. It imports only
  Lean's `Init`. The [checked Lean API reference](docs/api-reference.md) documents it.
- **The parser**, `packages/belay-sqlite-text`, which calls SQLite's own parser as native
  code while a file elaborates; see [the SQLite parser](docs/sqlite-parser.md).
- **The surface**, `packages/belay` (`Belay`, with `Belay.Sqlite`): the library that Lean
  developers import; see [its README](packages/belay/README.md).
- **The conformance evidence**: the frozen corpora under `conformance/`, which the
  conformance runner predicts with the model and the pinned native SQLite checks. The
  verdict job grades the claims in `judge/claims.json` against them.
- **Decisions** are the architecture decision records under `docs/`, named
  `adr-NNNN-*.md`. A change that adds or removes a capability starts as a record.
- **Tasks** are the task and status files under `plans/`, one pair for each piece of
  work that needs several commits.
- **Agent instructions** are in [`CLAUDE.md`](CLAUDE.md) and the workspace's `AGENTS.md`:
  the writing style, the checks and their cadence, and the review after each commit.
