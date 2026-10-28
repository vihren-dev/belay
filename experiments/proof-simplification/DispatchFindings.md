# Shared statement dispatch experiment

Date: 2026-10-26. Audience: designers and reviewers.
Base: `6413afe3ff50`. Production packages are unchanged.

## Question and scope

Can the existing table-atom dispatcher replace the two other complete
statement case analyses without stronger assumptions? Can the generic
database and plain-write facts replace their row-local copies?

This experiment covers the row-local atoms and distinct rowids. It does not
claim that unique keys or foreign keys fit `TableAtom`. Unique keys depend on
the catalog and table position. Foreign keys relate different tables.

## Experiments

`DispatchStatements.lean` contains:

- `rowLocalTableAtom`: the empty-table and sublist fields of `RowLocalAtom`
  supply `TableAtom`.
- `rowLocalStatement`: the exact assumptions and conclusion of
  `runStatement_rowLocal`, through `runStatement_tableAtom`.
- `distinctStatement`: the exact assumptions and conclusion of
  `runStatement_rowidsDistinct`, through `runStatement_tableAtom`.

Both statement proofs retain arbitrary clocks, counters, parameters and
resolved statements. Neither adds readiness, catalog validity, connection
configuration, or another database atom. The row-local proof retains the
conditional ADD COLUMN premise, including both refusal-flag values. Both
conclusions use the existing `Effect.Satisfies`, which requires preservation
for success and a carried constraint-FAIL database. Other errors require
nothing from the effect theorem.

The file imports neither old whole-statement module, directly or transitively.
It uses the existing plain INSERT, UPDATE and upsert proofs, the existing row
engine laws, and the existing generic statement dispatcher. It therefore
checks reuse of the dispatcher, not replacement of all plain-write proofs.

`DispatchPrimitives.lean` contains four applications of existing generic facts:

- `eachTableSetRows` derives the exact `Database.EachTable.setRows` claim from
  `Database.Every.setRows`, ignoring catalog and position in its fact.
- `keysUniqueSetRows` derives the exact `Database.KeysUnique.setRows` claim
  from the same theorem, retaining catalog and position in its fact. This
  result applies to row replacement only; it proves no schema-change law.
- `rowLocalCheckedWrite` derives the exact `checkedWrite_rowLocal` claim from
  `checkedWrite_satisfies` and the atom's constraint field.
- `rowLocalInsertOutcome` does the same for `insertOutcome_rowLocal` through
  `insertOutcome_satisfies`.

Each named experiment prints its axioms. Acceptance requires a Nix experiment
gate with no `sorryAx` or additional axioms; its result belongs in the design
status record. A direct Lean invocation is only a development diagnostic.

## Measured source reduction

Counts use physical source lines, including the signature but
excluding docstrings for declaration counts. A proof body starts after
`:= by`; the counts below contain no blank lines in those bodies.

| Statement proof | Original declaration / body | Experiment declaration / body |
| --- | --- | --- |
| `runStatement_rowLocal` | 65 / 58 | 22 / 15 |
| `runStatement_rowidsDistinct` | 74 / 71 | 17 / 14 |
| Total | 139 / 129 | 39 / 29 |

The shared adapter has four declaration lines, including its two field
assignments. These numbers show 100 fewer lines in the two case-analysis
bodies, before counting the adapter. They are not a prediction of net
repository deletion, build time, or compiled proof-term size. The generic
dispatcher remains unchanged. Other statement families still have their own
semantic work.

Run this from the workspace root to reproduce the declaration/body counts:

```python
from pathlib import Path
import re

model = Path("packages/belay-sqlite-model/Belay/Sqlite/Model")
cases = [
    (model / "RowLocalStatement.lean", "runStatement_rowLocal"),
    (model / "AdmittedDistinctStatement.lean", "runStatement_rowidsDistinct"),
    (Path("experiments/proof-simplification/DispatchStatements.lean"), "rowLocalStatement"),
    (Path("experiments/proof-simplification/DispatchStatements.lean"), "distinctStatement"),
]
for file, name in cases:
    text = re.search(r"(?ms)^theorem " + name + r"\b.*?(?=\n\n|\Z)", file.read_text())[0]
    body = text.split(" := by\n", 1)[1]
    print(name, len(text.splitlines()), len(body.splitlines()))
```

## Dependency causes and minimum boundary changes

The general abstractions were added above their specialized predecessors:

- `TableAtom` lives in `AdmittedAtomFrames`, which imports `RowLocalFrame`.
  That module imports `RowLocalAtoms`. Making `RowLocalAtom` depend on this
  location of `TableAtom` would create an import cycle.
- `RowLocalFrame` owns generic `Database.EachTable`, `Effect.Satisfies`, and
  its conversion helpers, alongside specialized row-local append support.
- `AdmittedPlainWrites` imports `RowLocalWrites` for
  `LiteralData.inserted_shape`. Therefore the generic checked-write proofs
  cannot replace row-local proofs in their current modules without a cycle.
- `Database.Every.setRows` lives among the row-engine facts. It already
  subsumes the copies in `RowLocalFrame` and `KeysUniqueFrame`.
- Generic DROP, nonwriting-statement and ADD COLUMN preservation facts have
  row-local names and locations even though their formulas do not require
  `RowLocalAtom`.

The dispatcher reuse itself compiles without module moves. Further removal
of the specialized primitive copies needs corrected import directions.
Module names are an implementation choice. These boundaries must hold:

- `TableAtom`, generic effect satisfaction and table/database frame facts
  do not import concrete atom instances or their statement proofs.
- Row-local evidence supplies the same empty/sublist facts once. It can
  extend `TableAtom`; no second general-purpose atom structure is needed.
- The generic plain-write layer owns or imports `LiteralData.inserted_shape`
  from below it. It does not import row-local plain-write specializations.
- Concrete atom instances and their local-write/ADD COLUMN facts depend on
  those primitives. Shared statement dispatch consumes those facts and
  `WriteLaws`.

The source import graph establishes the minimum changes more narrowly:
moving `TableAtom` below `RowLocalAtoms` permits direct shared fields; moving
`LiteralData.inserted_shape` below both plain-write modules removes the only
path from `AdmittedPlainWrites` to `RowLocalWrites`. To consolidate the unique-key
effect vocabulary too, move generic effect satisfaction below
`KeysUniqueFrame`: its current home reaches that module through
`RowLocalFrame → KeysUniqueCreate → KeysUniqueFrame`. By contrast,
`RowEngineFacts` imports neither frame module, so both `setRows` copies can
use `Database.Every.setRows` at its current location without an import cycle.
Moving that theorem is optional organization, not a correctness prerequisite.

Moving the required definitions and updating callers is sufficient for these boundaries.
No interpreter change, global registry, typeclass search system, or new
universal preservation framework is justified by this experiment.

## Implementation acceptance requirements

- The two old statement formulas remain derivable with exactly their old
  assumptions, including arbitrary raw resolved inputs. Tests compile these
  formulas using the shared proof and audit its actual axiom closure.
- There is one complete statement-constructor case analysis for this table
  atom path. Neither atom family retains a copied dispatch or calls its
  replaced whole-statement proof.
- There is one general implementation of the table replacement fact.
  Catalog/position-dependent instantiations remain possible.
- General checked-write and insert-outcome facts serve the row-local path.
  Their modules do not import specialized wrappers to obtain primitives.
- Plain-write and ADD COLUMN hypotheses remain distinct. Readiness is not
  introduced to hide missing plain-write facts.
- The production changes update all callers and delete replaced names and
  files, with no compatibility aliases. Useful theorem evidence can remain
  as a single certificate consumed by the generic run API.
- Statement behavior, rollback treatment, and constraint-FAIL carriers do
  not change. Existing conformance claims and judge inputs remain intact.

## Limits

This prototype does not perform the module moves or prove their import graph
after integration. It demonstrates theorem reuse against the frozen base.
It does not establish savings for foreign-key action proofs, unique-key
schema proofs, query laws, resolution, or the contextual run induction.
The implementation must account for concurrent name-trace changes when it
selects its integration base.
