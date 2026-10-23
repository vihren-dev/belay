# The local incremental build loop (ADR 0020)

Created 2026-10-22. Status: DONE (2026-10-22).
Status file: [status](20261022-local-build-loop.status.md).
Specification: [ADR 0020](../docs/adr-0020-local-build-loop.md), D1 to D6 and the owner
decisions.

## Outcome

1. **One package list, two shells.** A file under `nix/` holds the packages and the
   environment variables of the development shell. `nix/flake.nix` and the root
   `shell.nix` both take them from it. The flake dev shell is the same derivation as
   before the change. `shell.nix` adds the pinned toolchain, `BELAY_PARSER_LIBRARY` and,
   on Linux, `LEAN_CC`, and it is no longer a trial.
2. **direnv loads `shell.nix`.** `.envrc` keeps the resource check and loads `shell.nix`
   with `use nix`. It watches the files that `shell.nix` imports, so that a change of
   them loads the shell again.
3. **`just dev-build`** runs `lake build` in the packages under `packages/`, for the
   targets of D2: the model (`Belay.Sqlite.Model`,
   `Belay.Sqlite.Model.Codec`), the text package (`BelaySqliteText`,
   `BelaySqliteText:shared`, `parserShim:shared`, `belay-sqlite-translate`), the runner
   (`conformance-runner`) and the surface (`Belay`, `Belay:shared`). A second run without
   edits compiles nothing.
4. **`just dev-verdict [CORPUS...]`** builds the runner and the translation program as in
   item 3, copies them into `build/dev/runtime/.lake/build/bin/`, and runs
   `python -m judge run` with `python -m conformance.predict --runtime build/dev/runtime`
   as the subject: over all claimed corpora, or over the named ones with a reduced copy of
   the claims file under `build/dev/`. The judge writes the report to
   `build/dev/report.json`, prints its counts and failures, and sets the exit code. The
   recipe does not change `judge/`, `judge/claims.json` or the lock.
5. **Plain recipes, warnings, not checks.** Both are `just` recipes that run `lake build`,
   `cp` and the judge. Outside the shell of `shell.nix` (no `BELAY_PARSER_LIBRARY`), they
   print a warning that says how to get the shell, and run anyway: Lake's or the
   program's own error then shows what failed. (Amended 2026-10-22 by the owner: a first
   version in Python, with target arguments and checks before a build, was supporting
   code without a present problem.)
6. **Agent rule and texts (D5).** `AGENTS.md` has the rule of D5: the local loop while
   editing, the Nix checks before each commit, only Nix results as evidence, and direnv
   loads the shell. The first comment of the `justfile` says that direnv loads the shell.
   The README's direnv sentence says that `.envrc` loads `shell.nix`.
7. **ADR 0020 is ACCEPTED** and names this task.

## Tests

- The environment tests accept the new file under `nix/` and still refuse other files.
- A `requires_nix` test runs in the loaded shell of `shell.nix` and skips with a message
  outside it. It runs `just dev-build` twice and checks that the second run compiles
  nothing, starts the runner and the translation program, and runs `just dev-verdict` on
  one small corpus with exit code 0 and a report of only that corpus.
- One measurement for the pull request: on one commit, the counts of `just dev-verdict`
  equal those of `just verdict` for all corpora.

## Tricky points

- `tools/check_resources.py`, `tests/environment_snapshot_test.py`,
  `tests/test_resources.py` and the `upstream` suite in `build-support/tests.nix` list the
  files of `nix/` exactly. The new file must be in each list.
- The flake's `nixpkgs` comes from its input, and `shell.nix`'s from
  `build-support/locked-nixpkgs.nix`; both read the same lock. Compare the flake shell's
  `drvPath` before and after the change.
- Lake's no-op output: find how Lake reports the jobs that it ran, so that the test can
  check "compiles nothing".
- The agent session gets the new shell only after the owner runs `direnv allow` for the
  changed `.envrc` (ADR 0020, fact 8). The guard refuses `nix-shell`, so the shell of
  `shell.nix` cannot be tested in the session before that.
- The test recipes and CI keep the flake shell; `test-nix` in CI runs in it, so the
  `requires_nix` test skips there.
