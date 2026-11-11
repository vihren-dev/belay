# Task: move the Lean code into directories by division and team

Created 2026-11-10. DONE 2026-11-11 (status: `20261110-ownership-reorganization.status.md`).

## Problem

The directories of the packages did not show which part of the product a file belongs to. One file
often had declarations of unrelated parts, and an import could go from a basic part to a part that
uses it. A developer could not see from a path who owns the code.

## What must be true when the task is done

- Each Lean library of `packages/` has, below its root directory, one directory for each division that
  has code in it, and in it one directory for each team. The divisions, from the users to the base:
  Tooling, Programs, Schema, Queries, Frontend, Values, Shared.

  | Division | Teams |
  | --- | --- |
  | Tooling | Conformance, Counterexamples, ProofCost, SqlCommands |
  | Programs | Automation, Claims, Clock, Reasoning, Scripts |
  | Schema | Columns, Ddl, Dispatch, ForeignKeys, Rows, Triggers, Writes |
  | Queries | Automation, Evaluation, Fixtures, Preparation, Select |
  | Frontend | Codecs, Embedding, Grammar |
  | Values | DateTime, Json, Scalar |
  | Shared | Catalog, Execution, Resolved, Syntax, Values |

- A module that only collects imports, such as `Belay` and `Belay.Sqlite`, keeps its name.
- Each declaration of `packages/` is in a file of its division. A file with declarations of more than
  one division is divided, and each part keeps the file name.
- In one division, a part of a file is in the directory of its team when the part has at least 5
  declarations. A smaller part stays with the main part of that file in the division. Parts of one
  file that refer to each other in a cycle stay together, and a `mutual` block is not divided.
- Each file of `tests/surface` moves, as a whole, to the directory of the team that has most of its
  declarations (a team directory, or `Tests` of the division). It keeps its module name, the file name
  without `.lean`: the Python harness finds the file by its name below `tests/surface`. A data
  directory moves with the files that read it.
- No module of `packages/` imports a module of a higher division.
- The move changes no declaration: the names, types and source text are the same before and after.
  The permitted changes are `import` lines; the `namespace`, `end`, `open`, `set_option`, `variable`
  and `section` lines that a new file needs; the removal of `private` from a declaration that another
  file now uses; and the module name in a checked `{module}` reference. The compiled name of a
  `private` declaration contains its module, so it changes with the module.
- The Lake files, the Python tests, the mutant tables, the conformance files and the documents name
  the new paths and modules.
- The code of `experiments/` and `tools/` stays where it is; only its imports change.
- All Nix checks pass.

Not in this task: a change of the code that removes a reference between divisions.

## Tests

- A text check: the source text of each declaration is in the new tree as many times as before, and
  each changed line outside declarations is of a permitted kind.
- A declaration check: the built libraries have the same declaration names, kinds and types before
  and after the move, with the names of `private` declarations mapped to their new modules.
- An order check: no import goes up against the order of the divisions.
- A placement check: each declaration is in the division and team that the rules above give.
- `just test-full`, `just verdict`, `just test-nix` and `just test-scheduled-checks`.

The first four checks ran on the move itself and are not part of the repository.

## Points to know

- The name that the source uses for a declaration does not depend on its module. A move thus changes
  only `import` lines, not the references in the code.
- An `instance` or an attribute registration has no user that names it. A file that needs one must
  import the module that has it.
- Each new file adds header lines, against the goal of `docs/lean-simplification-goal.md`, which
  records the net change.
- `integrity/judge.lock.json` locks the judge. The move does not change the judge.
