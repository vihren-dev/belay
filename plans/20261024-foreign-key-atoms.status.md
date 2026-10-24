# Status: foreign-key facts and preservation

Created 2026-10-24. Status: OPEN. Split-API work is preserved; the accepted engine correction is queued.
Task: [task file](20261024-foreign-key-atoms.task.md).
Specs: ADR 0022 slice 5; ADR 0017 S6; ADR 0018 foreign-key execution rules.
Inspected base: PR #239, `98a07bfe`, in `vihren-dev/sqlite-verifier`.

## Owner decision and evidence

On 2026-10-24 the owner chose: "Split parent-schema compatibility and
row-reference validity into separate atoms, then revise the foreign-key API
and proofs." This replaces ADR 0022 D3's unconditional foreign-key preservation
claim. The accepted amendment and required outcomes are in the task and ADR.

The prerequisite audit used the pinned SQLite 3.51.0 executable from Nix.
DROP INDEX succeeds with enforcement on for a referenced parent's unique index;
the following `foreign_key_check` fails at prepare with a mismatch. The audit
also observed the repeated-primary-key example in the task: child `(1,99)` is
accepted against parent `(1,2)` because the selected `(a,a)` key uses child `x`
twice. These observations informed the specification; no task acceptance check
has run and no model implementation has changed.

The task therefore supplies an explicit comparison mapping for row truth and
a separate catalog compatibility fact. The convenience path keeps current
engine selection. Supporting-index removal can preserve the first fact under
mapping transport while breaking the second. The representation is left to the
implementer, with these observable requirements fixed.

## Progress and relevant files

- 2026-10-24: inspected the existing FK atoms/checks and `Resolution/ParentKeys`;
  recorded accepted semantics, two acceptance parts and Nix coverage requirements.
  The task lists the implementation files.
- 2026-10-24: review `20261024T122036Z-c64a44ba` found no musts and one should:
  the historical owner-decision list still named one atom. That entry now names
  the two atoms and the amendment date. Implementation remains pending.
- Implementation must be assigned to a separate jj workspace after task review.
  Coordinate model barrels, statement laws and the surface database export with
  S4 and the query-source task. No concurrent edits to those surfaces are allowed.
  Later ALTER and view statements extend the preservation matrix; their absence
  from the current language does not satisfy those future obligations.

## Part 1 implementation in progress

Workspace: `sqlite-verifier-fk-atoms`, based on `cf7aa9a6`. The coordinator reserved
FK entries in the model barrel and Lake module list, the surface database export,
and the two new test registrations. No shared ancestor was rewritten.

- `ForeignKeyMapping` supplies a total parent comparison for every child position
  and declared key. `ForeignKeyFacts` replaces the old atom with
  `RowReferencesHold` and `ParentSchemasCompatible`, table/database checks,
  decidability and equivalence laws. The surface exports both atoms and mappings.
- `ForeignKeyMappingLaws` relates declared keys to engine-selected links.
  `ForeignKeyCheckLaws` states selected-row correspondence. `ForeignKeyPrepareLaws`
  separates mismatch preparation from row generation and proves that compatible
  schemas imply no mismatch, without claiming its converse.
- `ForeignKeyRowFrame`, `ForeignKeySchemaFrame` and `ForeignKeyDropFrame` expose
  separate dependencies. The concrete DROP law transports positions with
  `keptBelow`; the schema law permits arbitrary row changes under a fixed catalog.
- Surface fixtures exercise the primitive/default paths, index-before-child
  transport, missing/unsupported parents, orphans, repeated columns and comparisons.
  Native differential fixtures classify recorded traces and replay kernel proofs.
  They are registered in the surface and model Nix suites.
- The full pragma statement-output law will reuse S4's `QueryStepOutput` and
  `SimpleQuerySteps` after coordinator integration. Part 1 is not complete without
  that law and its acceptance gates. Statement/run preservation is still part 2.

Before model edits, `nix-build integrity/judge.nix -A predictions --no-out-link
--dry-run` scheduled no build. The following cached invocation returned the
existing #239 output `/nix/store/4k77z378vnagzwx5448yqz0686d58cld-sqlite-verifier-predictions`.
This is reuse of the baseline, not a newly executed prediction build. No Nix
acceptance gate for this implementation has run; local builds and fixtures are
only development diagnostics.

## Accepted correction: repeated columns and NULL

The pinned 3.51.0 engine disagrees with the current model on a new combination:

```sql
PRAGMA foreign_keys=ON;
CREATE TABLE p(a,b,PRIMARY KEY(a,a));
CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));
INSERT INTO p VALUES(1,2);
INSERT INTO c VALUES(1,99);       -- succeeds, as required by the task
INSERT INTO c VALUES(99,NULL);   -- native SQLITE_CONSTRAINT at step
```

The current model accepts the last row. With enforcement off, store `(99,NULL)`
and run `PRAGMA foreign_key_check`: native reports a violation while the model
reports none. The new `repeated-unused-null-write` and
`repeated-unused-null-pragma` differential regressions retain the finding.
This is an observed specification/dependency issue, not acceptance evidence.

Pinned source `parser/upstream/sqlite3.c:135547` uses the selected `aiCol[i]` in
`fkLookupParent`'s NULL-test loop. At line 144165, the pragma uses selected
`aiCols[j]` when available, otherwise original `pFK->aCol[j].iFrom`. The current
`ForeignKeyLink.hasNull` always reads the original declaration columns. With the
repeated `(a,a)` parent key, the selected mapping reads child `x` twice; NULL in
unused `y` does not exempt the row. A missing target still uses original columns.

On 2026-10-24 the owner accepted the recommended shared-engine correction:
use the selected child projection for NULL tests, including repeated columns,
and retain declaration-column fallback when no comparison is selected. Revise
the atom defaults and proofs, and add native regression evidence. The revised
task and ADR22 are carried from the reviewed coordinator decision; review
20261024T135446Z-1c6eeb5e had no musts and its status-only should is resolved.
The preserved implementation above has not yet been changed for this decision.
Its source edits remain uncommitted and must be checked before completion.
