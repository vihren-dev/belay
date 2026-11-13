# Task: the table-rebuild example as a Lake project under `examples/`

Created 2026-11-13 (status: `20261113-examples-table-rebuild.status.md`).

## Problem

The README's table-rebuild example (`shop`, `badMigration`, `allSessions`, the check that answers
`false`, the database `found`, `fixedMigration` and the theorem `fixed_keeps_sessions`) exists only as
README blocks and as the test fixture `tests/surface/Schema/Tests/RebuildExample.lean`. A reader cannot
open it as a project, and the launch recording needs a project to open in an editor. The README tells
the reader to paste the blocks into a project.

Owner request, 2026-11-13: "Let's make an examples/ folder with this example. It should be a
fully-working lean project." Owner decisions: Belay is required by local path; if the library's
tactics do not prove the theorems in a few lines, the proof moves into the example (moved, not
copied); example-specific declarations never go into `packages/`.

The library's tactics do not prove the theorem: `sql_auto` fails on all routes, `sql_commute`
proves only `Migration.PreservesAt`, and its rule needs a migration without an INSERT from a query;
`#sql_check fixedMigration preserves allSessions on shop` answers `unknown`. The page for agents
already says that a read kept by a table rebuild needs a proof by hand.

## What must be true when the task is done

- `examples/table-rebuild/` is a Lake project: `lakefile.toml` that requires Belay by the path
  `../../packages/belay`, `lean-toolchain` equal to the one of `packages/belay`, a short `README.md`
  for users, and Lean files. `lake build` in the folder succeeds after a build of the packages.
- The main file has the names and the SQL text of the README blocks, in the README's order: the
  check of `badMigration` answers `false` with the README's counterexample, the two `decide +kernel`
  facts about `found` hold, and `fixed_keeps_sessions : fixedMigration preserves allSessions on shop`
  is a theorem whose axioms are only `propext`, `Classical.choice` and `Quot.sound`.
- The check `fixedMigration succeeds on shop` (answer `false`, a blob email) and the theorem
  `fixed_succeeds` with the premise `StrictRows` stay checked, in the example project.
- The proof modules that these theorems need are in the example project and nowhere else. The
  other fixtures that import them (`RebuildReplays`, `RebuildRefutation`, `SchemaRuleExamples`) keep
  their checks.
- The README points to the example folder from the example and install sections, and its links,
  the page for agents and the skill name the new places of the proof files.

## Tests

- `tests/surface_rebuild_test.py` keeps every check that it has now, on the moved modules, and
  pins the answers of the example's checks and the axioms of its theorems.
- A new test builds the example project with Lake from the installed packages (Nix runtime) and
  checks that the build succeeds, so the lakefile cannot rot.
- `tests/test_lean_categories.py` puts the example's Lean files in a build category.
- `tests/docs_test.py` checks the README's links.

## Key points

- `tests/surface_support.fixture_file` finds a fixture by its file name under `tests/surface`, and
  the fixture chain compiles a module named after the file stem. The proof modules keep their flat
  module names, so the example's lakefile lists them as roots.
- The surface suites of `build-support/tests.nix` copy only their listed inputs into the sandbox;
  the example folder must be an input, without its `.lake`.
- In the Nix runtime, Belay's manifest names Plausible by path, so a project that requires the
  installed Belay builds without network; in the development layout Lake fetches Plausible from git.
- The proofs are about `makeStrict`, `sample` and `RebuildGuide.allSessions`; the main file bridges
  to the README names with `rfl` and a catalog equality.
