# Status: the local incremental build loop (ADR 0020)

Created 2026-10-22. Status: DONE (2026-10-22).
Task file: [task](20261022-local-build-loop.task.md).
Specification: [ADR 0020](../docs/adr-0020-local-build-loop.md).
Source files: `shell.nix`, `nix/flake.nix`, `.envrc`, `justfile`, `tools/check_resources.py`,
`build-support/tests.nix`, `AGENTS.md`, `README.md`.

## Progress

- 2026-10-22: the task file. The flake dev shell's derivation before the change is
  `/nix/store/sicj83z1rdc77q5swkgklwzp5lx867h0-nix-shell.drv`.
- 2026-10-22: one package list, two shells (items 1 and 2). `nix/dev-shell.nix` holds the
  packages and variables; `nix/flake.nix` and `shell.nix` import it. The flake dev shell's
  derivation is unchanged on both systems (`sicj83z1…` on x86_64-linux, `2dg63zw2…` on
  aarch64-darwin). `shell.nix` differs from the trial only in the order of two packages.
  `.envrc` loads `shell.nix` with `use nix` and watches its inputs (all of `parser/` with
  `watch_dir`). README and team guide describe both shells. The four lists of the
  files of `nix/` have the new file. `just test-nix`: 67 passed.
- 2026-10-22: `just dev-build` and `just dev-verdict` (items 3 to 5) in `tools/dev_loop.py`,
  with `conformance.predict.RUNNER` naming the runner's path in a runtime root. The owner
  allowed the new `.envrc`; the session then had `LEAN_CC` and `BELAY_PARSER_LIBRARY`, and
  no new `/tmp/nix-shell.*` directory appeared. A no-op `dev-build` took 1.4 s; an appended
  definition in `QueryFunctions.lean` built 103 jobs in 31 s over the four packages.
  Measurement: `just dev-verdict` (58 s) and `just verdict` (61 s) on the same commit wrote
  identical reports for all 48 corpora (7,215 cases). Tests: `tests/dev_loop_test.py`
  (4 unit tests and the `requires_nix` test, which passed in the shell); `just test-source`
  454 passed; `just test-nix` 68 passed. The first comment of the `justfile` says that
  direnv loads the shell.
- 2026-10-22: the agent rule of D5 in `AGENTS.md` ("The local build loop"), item 6. The
  README's direnv sentence changed with the shell commit.
- 2026-10-22: DONE. ADR 0020's D1 names `nix/dev-shell.nix` instead of the trial.
  `just test-full` passed (742 s). Pull request: the implementation, on top of the ADR's
  pull request #203.
- 2026-10-22: after the owner's review, the checks before a build (shell variables, old
  `.lake/build` links) and the timeout handler are removed. Outside the shell the recipes
  warn and run; Lake's own errors show what failed. Task item 5 is amended.
