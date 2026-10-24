# Status: foreign-key facts and preservation

Created 2026-10-24. Status: OPEN. Split-API work and the accepted mapped-NULL and
mapped-action corrections are in progress; their checks remain.
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
twice. At that first audit, no task acceptance check had run and no model
implementation had changed. The later uncommitted split-API work is listed below.

The task therefore supplies an explicit comparison mapping for row truth and
a separate catalog compatibility fact. The convenience path follows engine
selection with the accepted NULL-test correction. Supporting-index removal can preserve the first fact under
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

## Initial part-1 implementation work

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
`repeated-unused-null-pragma` differential regressions retain the finding in
the FK workspace's uncommitted test file; they are not in a repository commit.
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
The preserved implementation was subsequently adapted as recorded below.
Its source edits remain uncommitted and must be checked before completion.
Carry review `20261024T141310Z-8526ed1f` had no musts and two status-only
shoulds. Marked the first audit as historical and the native regressions as
uncommitted. No source code was included in either planning commit.

## Resumed work and preservation prerequisite

The shared hasNull helper now uses selected child values for a located parent
and declaration columns for missing/mismatched targets. Mapping and atom docs
follow that meaning. Native regressions now cover INSERT, UPDATE, parent changes,
CASCADE, selected NULL and missing-target fallback. A pinned native-only replay
of 22 cases passed; it is diagnostic, not Nix acceptance. Model builds await the
S6 gate's shared build slot. The reviewed S4 query-output proof closure is carried
from `372e6c8f`, with matching module entries, for the full pragma statement law.
All implementation edits remain uncommitted until their checks pass.

A separate pinned native diagnostic found a required part-2 condition. Start
with `foreign_keys=ON`, parent `p(k TEXT UNIQUE)` containing `'1'`, and child
`c(x INTEGER REFERENCES p(k))` containing `1`. An AFTER DELETE trigger on p inserts
`'01'` when OLD.k is `'1'`. Deleting `'1'` succeeds, but foreign_key_check reports
`[c,1,p,0]`. Parent scans and child lookups apply different affinity rules, as
ForeignKeyMatch already documents. Enforcement, schema compatibility and selected
mapping alone therefore do not imply row preservation. The coordinator has the
exact setup and `build/agent-logs/fk-parent-affinity-diagnostic.log`; dependent
part-2 claims waited for specification assessment. The coordinator confirmed that
the task already permits this comparison-consistency premise and requires such
native necessity examples. Part 2 continues with an explicit named premise and
usable structural sufficient conditions; it must not assume final row truth.
The native case and a kernel fixture now retain the counterexample in WIP.

Carried the reviewed comparison-consistency clarification from coordinator
commit `98e1e8f13ecd8406cfabc48f1d5fe2870e9ca928` into only this task and ADR22.
Review `20261024T143702Z-98e1e8f1` had no findings. The source work above remains
uncommitted and separate from this planning carry. No acceptance check is claimed.

## Historical checks and action-target finding

The planning carry review `20261024T144605Z-befd2074` has no findings.
The atoms, transported row frames and full database/table pragma statement laws
compile in the local development build. The statement laws accept arbitrary
clock/index/counters/transaction state and state preparation separately from row
truth. Local build and test runs remain diagnostic until Nix acceptance.

Local focused checks passed 23 of 24 cases, including the surface theorem/axiom
fixture and all mapped-NULL cases except one action regression. The existing
`composite_null_checked` mutant was updated, with coordinator approval, to change
any to all on the selected child projection. All 49 local guard checks pass;
the focused mutant execution still remains.

The failing case exposes a second engine mismatch: with parent
`p(a,b,PRIMARY KEY(a,a))`, child `(x,y)` referencing `(a,b)` ON UPDATE CASCADE,
parent `(1,2)` and child `(1,NULL)`, updating parent a to 99 leaves native child
`(99,NULL)` but modeled child `(99,99)`. Both executions succeed. The shared
`actionCells` helper iterates declaration columns, but pinned sqlite3.c:136450
uses the selected aiCol[i] for action targets. Its assigned/changed-column inputs
also need assessment for triggers. The exact native/model observations are in
`build/agent-logs/fk-cascade-case.json`, `fk-cascade-prediction.json` and
`fk-cascade-summary.log`.

At this diagnostic boundary, the task authorized only the hasNull correction. The
coordinator has this additional finding and a recommendation to specify selected
targets for CASCADE/SET NULL/SET DEFAULT, including duplicate-column and trigger
effects. That dependent correction was paused; no action semantics had changed.
Independent frozen-prediction and atom-proof checks continue. No implementation
commit or task acceptance is claimed while a required regression fails.

## Accepted action correction and comparison premise

The owner accepted the selected-action-target correction on 2026-10-24. Carried
only the task and ADR22 from coordinator boundary `6d267b1e1d2aa4001b9711d63b3ac6516bb7b633`.
Review `20261024T151438Z-4c59fcc3` had no musts; its two wording findings were
fixed at that boundary. Follow-up `20261024T151547Z-6d267b1e` had no musts and
one status-only naming finding, whose resolution is carried with the reviews.
At this carry, the action source had not changed; the earlier pause was resolved.

The new comparison premise quantifies over all stored parent/child row pairs,
including future rows, and requires scan/lookup equality for non-NULL keys.
Structural sufficient conditions for a single BLOB parent with a nonnumeric
child and for a single TEXT/TEXT pair are proved. Kernel fixtures exercise both
and reject the TEXT/INTEGER example. Local builds and both surface fixtures
passed with 20 audited declarations; these are development diagnostics, not
Nix acceptance. Row preservation still needs the global immediate-counter
invariant through nested writes and FAIL. No part-2 completion is claimed.

The carry review `20261024T152143Z-1a10a3c8` had no musts and two shoulds.
The status header now names both execution corrections, and the unrelated task
line-wrap change is reverted. Action implementation is now in the uncommitted
working copy, using one selected projection for values, scans and action writes.
Its local build is in progress; it has no Nix acceptance evidence yet.

## Part-1 implementation checks before Nix acceptance

Follow-up scope review `20261024T152329Z-01a02bef` has no findings. The selected
projection now lives in Resolution/ParentKeys and is shared by NULL checks,
lookups, scans and action writes. Resolution/actionEvents gives assigned columns
to trigger preparation; actionWrites adds generated dependencies for FK checks.
Execution gives the same assigned/changed columns to RowWork.update. The
obsolete inverse pairIndex helper is deleted. The coordinator reserved the
three resolver files after confirming no conflict with the query-source agent.

Local dev-build and 37 focused checks passed: 35 native differential/kernel
probes and two surface fixtures with 20 axiom reports. New cases distinguish
unused declaration columns, UPDATE/DELETE SET NULL and SET DEFAULT, repeated
and reversed composite projections, rowid actions, assigned-column triggers,
generated constraint dependencies, and unused/generated-only trigger preparation.
The trigger fixture creates its two same-event triggers in the migration,
preserving the existing restriction on unknown trigger order in a starting schema.
Local dev-verdict also preserved all frozen claims. Logs are
`build/agent-logs/fk-dev-build-7.log`, `fk-focused-local-3.log` and
`fk-dev-verdict-2.log`. These results are diagnostic, not acceptance evidence.
Nix focused gates, the four FK mutants and part-1 full/verdict gates remain.
The build slot was handed to S4 after local checks completed.

## Part-1 focused Nix acceptance

The focused Nix gates passed on 2026-10-24, using sandbox=true,
sandbox-fallback=false and command-local max-jobs=1:

- `tests.model`, `PYTEST_ADDOPTS="-k foreign_key_atom_execution"`: 35 passed,
  160 deselected, 43.14 seconds. Output
  `/nix/store/mhvsqdz6wnx66s0rr80a12yp5xam6hif-sqlite-verifier-test-model-1`.
- `tests.surface`, `PYTEST_ADDOPTS="-k independent_foreign_key_atoms"`: two
  passed, 33 deselected, 3.61 seconds; 20 axiom reports admit only the three
  standard logical axioms. Output
  `/nix/store/k7vil77z5prkyc3a0i45h7vzv62nvhr4-sqlite-verifier-test-surface-1`.
- `scheduledTests.mutants`,
  `PYTEST_ADDOPTS="-k every_foreign_key_mutant_changes_a_verdict"`: one passed,
  18 deselected, 66.81 seconds; all four existing FK mutants were killed.
  Output `/nix/store/3773m5g75vhdvv3i94aa8y94ianw3d01-sqlite-verifier-test-mutants-1`.

Each command used `nix-build --expr` to override only PYTEST_ADDOPTS on the
named suite from `build-support/default.nix`. Logs are
`build/agent-logs/fk-nix-{model,surface,mutants}-1.log`. Self-review added five
module overview comments after the first two gates; the mutant runtime compiled
those final comments. No formula or execution behavior changed after the focused
model/surface gates. The required local dev-build was repeated for these comments.
Part-1 full/verdict gates and independent implementation review remain.

Part 2 remains open. Ignored Lean probes establish a total violation count from
existing pragma blocks, zero-count equivalence, and the end-of-statement bridge
from a counter bound. Another probe establishes parent-schema preservation for
current DML and statements that leave the catalog unchanged. These are development
diagnostics, not production laws or acceptance. The global counter bound still
must be derived through old/new row phases, actions and triggers. Its comparison
premise covers all future stored rows; intermediate storedness, unique parent
keys, update-key coverage and target stability must justify use at each phase.
The script bridge must carry the atom on saved snapshots as well as current rows.
