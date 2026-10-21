# The SQLite model moves to `Belay.Sqlite.Model` (ADR 0016, D3)

Created 2026-10-21. Status: DONE.
Status file: [status](20261021-model-move.status.md).
Specification: [ADR 0016](../docs/adr-0016-model-and-surface.md), D3 and "Order", step 1;
[ADR 0017](../docs/adr-0017-user-surface.md), D2 (S1, whose first code needs the name).

## Outcome

1. **The package.** The SQLite model is the Lake package `belaySqliteModel` in
   `packages/belay-sqlite-model`. Its libraries are `Belay.Sqlite.Model` (the model, root
   module `Belay.Sqlite.Model`) and `Belay.Sqlite.Model.Codec` (the wire format, root
   `Belay.Sqlite.Model.Codec`). Every module of the package is under `Belay.Sqlite.Model`, in
   `Belay/Sqlite/Model/`, and every declaration of the package is in the namespace
   `Belay.Sqlite.Model` or below it. The module that defines the database, `Belay.Sqlite.Model`
   today, becomes `Belay.Sqlite.Model.Database`, because the root takes its name.
2. **No old name stays.** No module, namespace, Lake package, path or Nix attribute of the old
   names (`Belay.Sqlite` outside `Belay.Sqlite.Model`, `belaySqlite`, `packages/belay-sqlite`)
   stays in the code, the build, the tests, the tools or the living documentation, and no alias
   of an old name exists. `Belay.Sqlite` itself is free for the surface (ADR 0016, D3).
3. **Every caller follows.** The verifier, the conformance runner (its namespace
   `Belay.Sqlite.Conformance` extends the model's, so it becomes `Belay.Sqlite.Model.Conformance`),
   the gate, the engineering examples and their approved baselines, the kernel tests, the Nix
   build, the conformance tools and their mutant anchors, the tests, CODEOWNERS, CI and the
   documentation inventory use the new names.
4. **No behavior changes.** The predictions of every frozen corpus are the same bytes as before
   the move, so every verdict stays the same; the judge, its lock, the claims and the corpora do
   not change.

## Tests

- `just test-full`, `just test-nix`, `just test-scheduled` and `just runtime-package` pass.
- The predictions (`nix-build integrity/judge.nix -A predictions`) before and after the move are
  equal file by file, and the locked `just verdict` passes.
- A search of the tracked files for the old names (outcome 2) finds only the historical
  records listed under "Key points".

## Key points

- **Historical records keep their text.** ADRs, the plans of finished tasks, review records,
  recorded corpora and experiment results describe the code at their time. They are not
  callers, and they keep the old names. The guide's repository `vihren-dev/belay-sqlite` and
  the Python package `belay/sqlite` are other things and keep their names.
- **The move is mechanical and one change** (ADR 0016, D3): a script does it, so that it can be
  run again on a new base if a branch below it changes. It comes before the first surface
  code, so no surface module has to move.
- **Model work in flight.** ADR 0016 (amended 2026-10-21, "Order") lets a script prepare the
  move as a local commit on top of model work in review; its pull request opens only when no
  model pull request below it is open, and the script runs again on that base. The pull
  requests of ADR 0018 (#204 and #205) are open, so the move is a local commit on top of them
  until they merge.
- **Text that names the package by parts.** The mutation tools rewrite `namespace Belay.Sqlite`
  and `end Belay.Sqlite` in copied files, Python code builds paths as
  `packages/belay-sqlite/Belay/Sqlite`, and the mutant tables name files from
  `belay-sqlite/Belay/Sqlite/`. Each must name the new path and namespace.
- **Approved baselines.** The engineering examples' `approved/baseline.json` records the
  SHA-256 of each approved file; a changed `open` or name in an approved file needs its new
  digest.
- **Lake state.** The new path makes old Lake caches miss (`build/lake-test-cache`,
  `.lake` folders); the first builds after the move are full builds.
