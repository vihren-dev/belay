# Task: `succeeds … on schema`, and the public rebuild example as a fixture

Created 2026-11-13 (status: `20261113-succeeds-on-schema.status.md`). Issues #382 and #384, launch
blockers.

## Problem

`M succeeds` is `Succeeds M (fun _ => True)`, a claim about every database, and `M succeeds where G`
adds an SQL guard. No short form says "on every database with the schema `shop`", which #375 added
for `preserves` (`M preserves Q on shop`). The README tells the user to state `succeeds` together
with `preserves`, so both claims need the same form (#382).

The rebuild example of the README is proved in the repository with the long forms and the names
`makeStrict` and `makeStrictWrongEnforced`. No fixture states it with the names and the notation of
the public example, so CI does not show that the short forms work on it (#384).

## What must be true when the task is done

### Notation (#382)

- `M succeeds on S` elaborates to `Succeeds M (fun db => db.HasCatalog S)`, and
  `M succeeds on S where G` to `Succeeds M (fun db => db.HasCatalog S ∧ Holds G db)`, with the same
  shape as `preserves … on S [where G]` (`MigrationPatternSyntax.lean`).
- `M succeeds` and `M succeeds where G` keep their meaning, and a guard that is not one read-only
  statement keeps its error at the guard's source position.
- `#sql_check M succeeds on S` searches the databases of the schema `S` without
  `with (schema := …)`: it reads the schema from the premise, as for `preserves … on S`.
- The primitive `Succeeds M P` with any predicate stays available.
- The documentation of `succeeds` (the docstrings, `packages/belay/README.md`, the table of the root
  `README.md`, the page for agents and the skill) shows the `on` form beside the form without a
  premise.

### Fixture (#384)

A surface fixture that CI compiles states the rebuild example with the schema `shop`, the wrong
rebuild `badMigration`, the fixed rebuild `fixedMigration` and the read `allSessions`:

- `#sql_check badMigration preserves allSessions on shop` answers `false` with one customer and one
  session; the test pins the answer and its counterexample.
- `#sql_check fixedMigration succeeds on shop` answers `false` with a customer whose email does not
  fit the STRICT type (a blob); the test pins the answer and its counterexample.
- `theorem fixed_keeps_sessions : fixedMigration preserves allSessions on shop`.
- `theorem fixed_succeeds : Succeeds fixedMigration (fun db => db.HasCatalog shop ∧ StrictRows db)`.
  The premise on the rows stays a Lean predicate; an SQL guard for it is #383, not this task.
- Both theorems reuse the existing rebuild proofs (`RebuildKeeps.lean`, `RebuildSucceeds.lean`)
  and show only the standard axioms.

## Tests

- `tests/surface/Programs/Tests/SuccessSyntaxExamples.lean` (run by `tests/surface_success_test.py`):
  the expansions of the two `on` forms by `rfl`, and the guard error positions.
- The new fixture, run by a test in `tests/surface_rebuild_test.py`, which pins both check answers
  and the axioms of both theorems.
- The whole suite: `just test-full`.

## Tricky points

- The existing rebuild theorems take the premise `db.raw.catalog = sample.raw.catalog`, where
  `sample` has rows and its own SQL text. `HasCatalog shop` is `db.raw.catalog = shop.raw.catalog`;
  the catalog keeps the text of each `CREATE`, so the two premises agree only when the texts agree.
- The syntax `term:21 " succeeds"` and `" succeeds" " where "` are two syntaxes today. An optional
  `on` must not make `M succeeds where G` or a trailing `M succeeds` parse differently.
- `#sql_check` names the migration in its replay lines (`makeStrictWrongEnforced, statement 1: …`);
  the fixture's answers name `badMigration`.
- New test modules must be listed in `tests/nix_suites.json`.
