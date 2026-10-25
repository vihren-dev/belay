# Status: foreign-key facts and preservation

Created 2026-10-24. Status: OPEN. Part 1 (split API and accepted mapped-NULL/action
corrections) is accepted. Part 2's row/action/trigger induction and conditional
DML/run and CREATE/plain-DROP laws are integrated with the enforced-DROP proof unit.
Their focused Nix gate passed; integration review `20261025T001914Z-dd60f94c` found no musts.
The ADD COLUMN execution correction is implemented and Nix-checked. ADD COLUMN
preservation laws, complete DDL/run conditions, the full matrix, part-2 acceptance and
separate corpus-v54 evidence remain open.
Task: [task file](20261024-foreign-key-atoms.task.md).
Specs: ADR 0022 slice 5; ADR 0017 S6; ADR 0018 foreign-key execution rules.
Inspected base: PR #239, `98a07bfe`, in `vihren-dev/sqlite-verifier`.

Latest scope decision, 2026-10-25: the owner accepted correcting ADD COLUMN
REFERENCES defaults, including empty/nonempty tables, enforcement on/off and
literal-NULL versus NULL-valued expression distinctions. ADR22 and the task are
amended together. Native evidence is retained in the FK workspace's
`build/agent-logs/add-reference-{native.json,model.log,default-spelling-native.json}`.
The enforced-DROP unit is checked and reviewed at `ffe4d749`. The execution
correction is implemented in the commit "Refuse ADD COLUMN of a REFERENCES column with
a non-NULL default on a populated table" (details in the section "ADD COLUMN execution
correction (part 2, unit 1)" below); its focused Nix gates passed. The ADD COLUMN
preservation laws, the unified DDL/run contract and the matrix remain open. The
task-amendment review `20261025T015343Z-fc22761c` found no musts and one R19 should
(name the correction in the acceptance-part list); that is done and is historical.

Prior scope decision, 2026-10-24: the owner accepted selected action targets
for CASCADE/SET NULL/SET DEFAULT and their assigned/changed-column effects.
Native diagnostics show repeated-key actions leave an unused child column
unchanged and do not fire its UPDATE OF trigger. The earlier model wrote that
column too. The revised task requires regression evidence and ordinary-mapping
coverage. The focused native Nix gate now passes; full part acceptance remains.

Review `20261024T151438Z-4c59fcc3` found no musts and two wording shoulds:
name both execution corrections in the acceptance boundary and state explicitly
that the action-target correction had not started at that boundary. Both were corrected.

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
- Implementation was assigned to a separate jj workspace after task review.
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

Implementation commit `892670085cd1b944eae4da8f7b4af60197ab6f37` received review
`20261024T155358Z-89267008`: no musts and one should. The ADR amendment's obsolete
“planned, not implemented” wording now points to its part-1 implementation record.
The reviewer explicitly skipped some files and docstrings, so a supplementary
review of the same implementation is required before part-1 acceptance.
The source stays at rest in this workspace; part-2 counter proofs start in the
separate `fk-preservation` workspace based on that implementation commit.

The ADR wording fix is `1183e81c45b7b0af6d6252190537d845e0239e9a`; review
`20261024T155658Z-1183e81c` has no findings. Supplementary implementation review
`20261024T160106Z-89267008` read all production changes, including the full
Query*Output, SimpleQuery, StatementCalm, ForeignKey*Frame and ForeignKey*Laws
files. It found four documentation shoulds in the carried S4 closure, now fixed:
QueryStepOutput, OutputResultsLaws and StatementCalm describe the model without
its surface consumer, and SimpleQuerySteps distinguishes faultless subquery
variants from plain variants. The required local dev-build passed after these
comment-only edits; this is diagnostic, not Nix acceptance. No formula changed.
The remaining review scope is exactly ForeignKeyAtoms.lean,
ForeignKeyComparison.lean and all 35 probes in foreign_key_atoms_native_test.py;
a bounded supplementary review of those files is running.

Test-only review `20261024T160318Z-89267008` fully read the three remaining files,
including all 35 native probes, and found one docstring should: the nonunique
parent fixture has a NULL child row, while the others have empty children. That
wording is corrected. The documentation-fix review `20261024T160408Z-c0dc0674`
found one should: all SimpleQuerySteps variants require Calm, including faultless
variants. Its module overview now states that shared premise explicitly. Local
dev-build and both surface fixtures passed after these comment changes; acceptance
remains the Nix evidence above, with full/verdict still pending. The combined
implementation reviews now cover every changed production and test file in full.

The final comment review `20261024T160619Z-5cdfd600` was clean (zero musts and
zero shoulds). Part-1 `just test-full` then stopped at the documentation inventory:
ForeignKeyDropFrame had duplicated `Catalog.tableAt_drop_kept`, already defined
in DatabaseShapedLaws. This was an implementation defect, not an environment
failure. The duplicate is deleted; the DROP frame now imports and uses the
existing shared theorem. The correction changes no formula or execution result.
Its required local dev-build and both focused surface fixtures passed as diagnostic
checks (`fk-dev-build-11.log`, `fk-local-atoms-11.log`). Independent review and the
full/verdict acceptance rerun follow; the failed gate did not run verdict.

## Part-1 acceptance complete

The duplicate-law correction at `3df8e64142627707a4ac42d8e06b048d5629b73e`
passed independent review `20261024T161455Z-3df8e641` with zero musts and
zero shoulds. The complete review coverage is the union of implementation
reviews `20261024T155358Z-89267008` and `20261024T160106Z-89267008`, test-only
review `20261024T160318Z-89267008`, and the clean follow-ups recorded above.
The test-only review covered exactly `tests/surface/ForeignKeyAtoms.lean`,
`tests/surface/ForeignKeyComparison.lean` and all 35 cases in
`tests/foreign_key_atoms_native_test.py`; the supplementary implementation
review read every changed production file in full. All findings are resolved.

The sequential Nix acceptance command used command-local max-jobs=1 and finite
timeouts: `timeout 2400 just test-full`, then `timeout 1800 just verdict`.
The owned process 36195 completed with exit 0 on 2026-10-24. Full passed 826
tests with zero failures, errors or skips. Reports:
`/nix/store/j8fbmdz188sgyksxqbcgzmiawh4x60mj-sqlite-verifier-test-reports`.
The full model and surface suite outputs are
`/nix/store/miay3482a3z44pkkmmka18bjkl78lkc3-sqlite-verifier-test-model-1` and
`/nix/store/q8kb41mfdf4x8jmi3nl7y35rpnj7pwkg-sqlite-verifier-test-surface-1`.
Verdict preserved all frozen claims; output:
`/nix/store/1mnxx4jshvv7zp58jzds5vi7rasss88v-sqlite-verifier-verdict`.
Logs are `build/agent-logs/fk-part1-{test-full,verdict}-2.log`.

All 53 prediction files, containing 7,372 cases, byte-match the baseline
`/nix/store/4k77z378vnagzwx5448yqz0686d58cld-sqlite-verifier-predictions`.
The current prediction derivation is
`/nix/store/8cax62kyxx2lv55za3dqyw4inzhaz0d4-sqlite-verifier-predictions.drv`;
its output is `/nix/store/axvw8k3lgld2iliglw0yn8dxn526m9x4-sqlite-verifier-predictions`.
There are no changed, added or removed frozen predictions to classify. The
selected-column corrections are exercised by the 35 native differential cases
and the focused FK mutation gate recorded above. No judge or lock file changed.
The reserved corpus-v54 judge extension and part-2 preservation remain open.

Part 2 continues only in the isolated `fk-preservation` workspace. A checked
proof probe now connects actual oldSteps and physical deletion to the global
counter bound, including self-references, under explicit storedness, rowid
uniqueness, row alignment and lookup/scan consistency premises. This is local
development progress, not acceptance or a completed action/trigger invariant.
The heavy slot was returned to the coordinator after acceptance terminated.

## Part-2 counter and schema proof unit: preparation record

The separate `fk-preservation` workspace retains the reviewed part-1 correction
files and records through `02a6498c`, without rebasing shared ancestors. Its
new source is proof-only: a total violation count, zero-count equivalence,
end-of-statement success/FAIL bridge, counter bookkeeping, exact old-row scan
arithmetic, and the global bound through physical deletion. The deletion law
includes self-references and uses explicit alignment, storedness, target-rowid
uniqueness and lookup/scan consistency premises; it assumes no final row fact.
Separate schema laws cover data writes and unchanged-catalog statement/run paths,
including the saved-snapshot premise. They do not claim general DDL preservation.

The maintained kernel fixtures distinguish an unchecked raw UPDATE from a resolved
UPDATE, cover cascade and rollback schema behavior, apply the generic deletion
law to a checked self-reference, and check the pending orphan count after a
parent deletion. New proof modules and fixtures compile in direct Lean diagnostic
probes, with only the three standard logical axioms. These local probes are not
Nix acceptance. At this preparation checkpoint, the mandatory dev-build and focused
Nix fixture gate were queued for a resource-slot release. Their later completed
acceptance is recorded below; the new-row, update coverage, action and trigger
induction remains in progress.

The three-line SimpleQuerySteps overview correction from reviewed S4 boundary
`c11a1f83fed9e8eae8d6234201050bc6b741cc00` is carried exactly: the faultless
no-error law permits source faults, while the has-rows/no-rows equivalences need
a fault-free source. This documentation-only correction changes no theorem.

## Counter/schema/deletion unit acceptance

The focused Nix surface gate passed on 2026-10-24: five fixtures passed, 33
deselected, 8.53 seconds. The output is
`/nix/store/kd5kljc36w937bizkhpdvjqnky08bzsh-sqlite-verifier-test-surface-1`.
The gate compiled the model, text and surface package closure and checked 61
axiom reports across the existing atom/comparison fixtures and the new counter,
schema-run and deletion fixtures. Every report admits only propext,
Classical.choice and Quot.sound. Command: `timeout 1800 nix-build --no-out-link
--option sandbox true --option sandbox-fallback false --extra-experimental-features
"nix-command flakes" --expr 'let project = import ./build-support/default.nix {};
in project.tests.surface.overrideAttrs (_: { PYTEST_ADDOPTS =
"-k independent_foreign_key_atoms"; })'`, with command-local max-jobs=1.
Log: `build/agent-logs/fk-part2-nix-surface-1.log`; owned process 35480 exited 0.
The mandatory dev-build also completed before this gate; its local result is
not acceptance evidence.

This coherent proof unit contains ForeignKeyCounter, CounterOld, CounterRun,
CounterScans, LookupRemoval, CountRows, CountRemoval, CountDelete, SchemaWrites
and SchemaRuns under the common ForeignKey prefix. Each file is below 200 lines.
The maintained fixtures cover both the self-row exclusion and a retained child's
pending violation, rather than only restating the generic theorem. Independent
review follows this commit. New-row arithmetic and append lemmas remain ignored
probes for the next unit; they are not included in this acceptance. The full
action/trigger/update invariant, DDL/mapping conditions, combined run laws and
atom-by-statement matrix remain open, so the task remains OPEN.

Independent review `20261024T170420Z-54c9c112` read the full coherent unit and
found zero musts and two status-only shoulds. The header now distinguishes
accepted part 1 from open part 2, and the pre-gate paragraph is marked as a
historical preparation checkpoint. Both findings are resolved. The source
commit remains `54c9c112f4ffe1038e84e9d5846a18254c540759`; its Nix evidence above
is unchanged. No heavy process is active here; slot 1 returned to the coordinator.

## Insertion proof unit: preparation

The next unit adds an exact global count equation for physical append and the
counter bound through actual newSteps with no stale UPDATE row. It includes
self-references, either parent-scan flag, storedness, row alignment, uniqueness
of the enlarged table and the selected-key/lookup-scan comparison conditions.
A separate self-lookup premise compares the engine shortcut with ordinary lookup
for every future stored row; rowid, BLOB and matching stored-affinity structural
laws discharge it. No condition assumes the final row-reference atom.

The maintained insertion fixture applies the generic law to a self-reference,
repairs an orphan with its new parent, and gives a raw duplicate-parent example
where the counter would otherwise erase an unrelated orphan. All seven proof
files and the fixture have fewer than 200 lines. Direct Lean probes compiled
these sources and their 34 axiom reports; those diagnostics are not acceptance.
The mandatory dev-build and focused Nix gate are queued for a resource-slot
release. Updates with stale rows, action/trigger induction and the remaining
statement/run/DDL matrix are still open.

The insertion unit's sequential gate completed on 2026-10-24 with exit 0
(owned process 88073). The focused Nix surface suite passed six fixtures,
33 deselected, in 8.50 seconds. Output:
`/nix/store/afgmspdjm1andpc3pd1wlfqdv9gl4bib-sqlite-verifier-test-surface-1`.
The six fixtures check 95 axiom reports, including all 28 new exported theorems
and six insertion-fixture laws; only the three standard logical axioms occur.
Command: `direnv exec . bash build/agent-logs/fk-insertion-gates.sh`, which ran
`timeout 900 just dev-build` followed by the same sandboxed Nix surface expression
as the previous unit, with command-local max-jobs=1 and timeout 1800. Logs:
`build/agent-logs/fk-insertion-{dev-build,nix-surface}-1.log`. The dev-build is
local diagnostic evidence; the Nix result above is the acceptance evidence.
Slot 1 was released to the coordinator after terminal completion.

A separate next-unit audit found two input/effect necessities. A raw Valid row
can contain a stale generated cell, so UPDATE coverage needs an explicit
consistent-generated-values input condition. More significantly, pinned native
SQLite 3.51.0 and a direct kernel probe both allow an unrelated pending orphan
counter to be cancelled by a level-1 self-parent UPDATE scan over a stale row.
The general UPDATE/trigger proof branch is paused for coordinator review of its
additional condition. This does not affect the checked insertion law, which has
no stale row. Native scripts and records are diagnostic findings, not Nix
acceptance for this unit; no execution or judge file changes are included here.
The full preservation task remains OPEN.

Independent review `20261024T173427Z-45a65a92` completed with zero musts and
zero shoulds for insertion source commit
`45a65a92de030a76f152240840f703d09a025cc1`. No source correction was needed.
The coordinator confirmed that outcome 6 already permits the necessary input
and allowed-effect conditions, so the stale-self-scan finding contradicts no
promised unconditional API. No owner question is pending. The UPDATE branch
continues with an explicit restriction for level-1 stale self scans and structural
sufficient conditions; execution remains unrestricted and unchanged. The native
and kernel counterexample will be retained in that unit. Next work is isolated
in `fk-update-preservation`; this insertion checkpoint is at rest.

## UPDATE phase proof unit: preparation

The next coherent unit composes actual selected oldSteps/newSteps counter deltas
with the physical replacement count. It does not assume the bound while the old
row is temporarily removed. Omitted child/parent checks cancel through explicit
cell-equality facts; a separate frame gives exact violation-count equality when
all FK-read cells stay unchanged. Stale self lookup has a key-agreement premise.
Parent scans require either no stale row or no processed self-child link, because
the native stale-self diagnostic can cancel an unrelated pending violation.

Seven proof modules and two fixtures have been promoted in the isolated
`fk-update-preservation` workspace. Every new file is below 200 lines. Direct Lean
diagnostics checked their Verso documentation and the successful changed-child
bound, unchanged payload frame, resolved UPDATE runs, stale-self failure and its
two level-2 neighbors, and a raw stale-generated-cell counterexample. These local
checks are not acceptance evidence. The fixtures audit 26 exported theorems and
10 concrete laws; the focused Nix suite will audit 131 reports in eight fixtures.
The mandatory dev-build and Nix gate are queued for a coordinated resource slot.
The script is `build/agent-logs/fk-update-gates.sh`, with finite timeouts and
command-local max-jobs=1. No execution, judge or task-specification change is made.

This remains an intermediate phase-law boundary. General resolved changed-column
coverage, the actual row/action/trigger induction, DDL and mapping-transport
conditions, combined statement/run laws and the atom-by-statement matrix remain
open. The raw generated-cell witness demonstrates an input-condition necessity;
it is not a native-reachable database claim. The pinned stale-self native record
is at `/home/codex/work/research_notes/Lean model modularity investigation/fk_stale_self_scan_native_20261024.json`;
its three cases are diagnostic evidence for the eventual separate authored corpus.

The UPDATE phase gate completed on 2026-10-24 with exit 0 (owned process 68995).
The focused Nix surface suite passed eight fixtures, 33 deselected, in 11.21 seconds:
`/nix/store/5hwflhzkfbfz7607j3i2q8i2mmq9w873-sqlite-verifier-test-surface-1`.
The suite checks 131 axiom reports, including all 26 new exported theorems and
10 UPDATE fixture laws; only the three standard logical axioms occur. Command:
`direnv exec . bash build/agent-logs/fk-update-gates.sh`, which ran
`timeout 1200 just dev-build`, then the sandboxed focused Nix surface expression
with timeout 1800 and command-local max-jobs=1. Logs are
`build/agent-logs/fk-update-{dev-build,nix-surface}-1.log`. The local build is
diagnostic evidence; the Nix result is the acceptance evidence. Slot 2 returned
to the coordinator at terminal completion. Independent review follows this commit.
The next coverage proofs are isolated in `fk-update-coverage`; the full
statement/run preservation task remains OPEN.

Independent review `20261024T183647Z-78a6dbc2` checked all seven proof modules,
the exports and package registration, both fixtures, their test parametrization
and this status update. It found zero musts and zero shoulds. Source commit:
`78a6dbc24d1f1bc1f1713245140a316c5482407a`. No correction was needed. The accepted
UPDATE checkpoint is at rest while assignment/mapping coverage proceeds separately.
The coordinator selected published repaired PR #243 head
`2cb4c5e3af6f59b8a6fae5a584ac4e536450c87d` for the next integration boundary;
it includes repaired #242 and the derived-source publication without unfinished
S4 work. No task-end or part-2-wide acceptance is claimed here.

## Assignment and mapping coverage: preparation

The next unit derives the UPDATE phase's omitted-check premises from the actual
catalog-selected mappings and assignment constructors. The five proof modules
ForeignKeyMappingCoverage, ParentCoverage, AssignmentCoverage, UpdateCoverage
and ActionCoverage connect declared columns to selected child/parent cells,
level-zero processing to the exact frame, literal action targets to their
reported columns, and unassigned aliases to unchanged rowids. Each file is below
200 lines. The generic cell premise remains available; the assignment bridge
requires a nongenerated column only at the cell whose unchanged value it proves.
Raw stale generated cells still need the explicit input/effect condition already
recorded above. This unit changes no execution definition or validity atom.

The focused coverage fixture applies the laws to an ordinary payload UPDATE,
a repeated selected parent key, all three writing action forms and a rowid alias.
It audits 27 exported theorems and six fixture laws. Together the nine FK fixtures
will audit 164 reports. Direct Lean diagnostics checked the five modules, checked
Verso references and fixture; all 33 new reports use only the standard logical
axioms. The source import/glob boundary diagnostic also passed. These are local
diagnostics against the prior runtime and do not establish integration acceptance.
Before the gate below, the merged source still required dev-build and the focused Nix gate.

This workspace merges reviewed FK checkpoint `62aebf43` and published repaired
query-source head `2cb4c5e3af6f59b8a6fae5a584ac4e536450c87d`. Four documentation
conflicts were resolved without formula changes: OutputResultsLaws and
QueryStepOutput take the published descriptions; SimpleQuerySteps and StatementCalm
retain the previously reviewed corrections to overbroad context claims. Lake
module registration and the Nix fixture inventories retain both sides, excluding
the replaced ForeignKeysHold entry. The query-source status uses the published
record. These resolutions are included in the next independent review. There
were no runtime-definition conflicts. No unfinished S4 ancestors are included.

The prepared sequential gate was `build/agent-logs/fk-coverage-gates.sh`, with
finite timeouts and command-local max-jobs=1. It was queued for an explicit
resource-slot grant before the completion recorded below. The actual row/action/trigger induction and the remaining
statement/run/DDL matrix remain open; this is another intermediate proof boundary.

The coverage gate completed on 2026-10-24 with exit 0 (owned process 19614).
The focused Nix surface suite passed nine fixtures, 52 deselected, in 12.21 seconds:
`/nix/store/3g9f88912zp62a3pks9gb5s47j4jhisx-sqlite-verifier-test-surface-1`.
It checked 164 axiom reports, including all 27 new exported theorems and six
coverage-fixture laws; only the three standard logical axioms occur. The command
was `direnv exec . bash build/agent-logs/fk-coverage-gates.sh`, which ran
`timeout 1200 just dev-build`, then the sandboxed focused Nix surface expression
with timeout 1800 and command-local max-jobs=1. Logs are
`build/agent-logs/fk-coverage-{dev-build,nix-surface}-1.log`. The local development
build is diagnostic evidence; the Nix result establishes this merged unit's
acceptance. Slot 1 returned to the queued CTE build on terminal completion.
Independent review follows and includes the four documentation conflict
resolutions, both inventories, all five coverage modules and the fixture. The
row/action/trigger induction continues separately in `fk-engine-counter`.

Independent review `20261024T185616Z-0b3f6334` checked the merge and coverage
source commit `0b3f633498c32c254262997b474e1c18f9d9c127`. It found zero musts and
one R19 status-wording should: two preparation paragraphs still described the
now-completed gate as pending. Both now use past tense. The reviewer found no
source issue, confirmed the 27 theorem plus six fixture audit inventory, and
checked the conflict resolutions and retained derived-source registration.

## Actual row-engine counter induction

The `fk-engine-counter` unit adds 14 proof modules, each below 200 lines, and two
focused fixtures. The shared invariant combines admission, unique keys and a bound
on all catalog-selected FK violations by the immediate counter. The proofs follow
the existing row engine through DELETE, UPDATE, INSERT, replacement deletion,
credited nested calls, foreign-key actions, trigger steps/programs and the full fuel
induction. No interpreter or execution definition is added or changed. The final
`rowsKeys_rowReferences` theorem applies the counter-zero publication rule to
successful writes and retained partial FAIL states. Rollback carriers retain the
input database facts, but the later SQL bridge must establish row validity on the
saved snapshot that it restores.

The conditions remain explicit. Catalog comparison facts quantify future stored
values, including intermediate action and trigger writes. UPDATE coverage applies
to actual assignment constructors and their changed-column closure. A continuing
BEFORE UPDATE sequence must retain the target rows; the row wrapper derives old-row
retention from that named frame. Empty BEFORE programs are a sufficient helper.
Generated UPDATE work has its own cell/rowid coverage and stale-self-scan conditions;
none of these premises asserts the desired final row-reference atom. The existing
mixed-affinity, stale-self-scan and raw stale-generated-cell witnesses still explain
the substantive restrictions. Generic result/fold helpers use the existing monadic
execution and admission/write laws.

The engine fixture proves the closed theorem for a parent UPDATE with a real
CASCADE child update, then checks both actual success and an AFTER child trigger's
FAIL result that retains the changed parent and child. Structural BLOB comparison
and assignment lemmas discharge its universal conditions; final row validity is not
a premise. A separate fixture audits all 33 new exported theorems. The six concrete
fixture laws also have axiom audits. Direct Lean and layer checks were diagnostics;
they are not acceptance evidence.

The sequential gate completed on 2026-10-24 with exit 0 (owned process 51552).
Command: `direnv exec . bash build/agent-logs/fk-engine-gates.sh`. It ran
`timeout 1200 just dev-build` and then the sandboxed focused Nix surface expression
with `PYTEST_ADDOPTS="-k independent_foreign_key_atoms"`, timeout 1800 and command-local
max-jobs=1. The Nix suite passed 11 fixtures, 52 deselected, in 13.62 seconds:
`/nix/store/grsxi5rjsqz0w3311nf5xv3l2yiilv6m-sqlite-verifier-test-surface-1`.
All 203 reports use only `propext`, `Classical.choice` and `Quot.sound`. Logs are
`build/agent-logs/fk-engine-{dev-build,nix-surface}-1.log`. The development build
passed as a local diagnostic; the Nix result establishes this unit's acceptance.
Slot 2 returned to the coordinator at terminal completion. Independent review
follows this commit.

This is an intermediate part-2 boundary. The actual statement/run bridges,
enforcement-off frames, DDL/mapping-transport conditions, combined atom laws and
atom-by-statement matrix remain open. Ignored local probes continue in the separate
`fk-statement-preservation` workspace; no task-end acceptance is claimed here.

Independent review `20261024T194322Z-a4521575` covered the 14 new modules, model
barrel/lake registration, status, fixtures and their parametrized audit counts. It
found zero musts and zero shoulds. Source commit:
`a4521575ed4d1693680dd6fa527bfbbe8b62f2d3`. No correction was needed. The reviewer
did not rerun the checks or independently sum the 203 reports; the passing Nix
fixture assertions enforce the exact per-case counts
`14+6+13+8+20+34+30+6+33+6+33 = 203`. This accepted source is at rest while the
statement/run and enforcement-off frame probes continue separately. The later
statement matrix will distinguish successful enforced UPSERT DO NOTHING from the
current undescribed DO UPDATE path; the wrapper theorem does not promise a
successful result in that excluded branch.

## Conditional statements and transaction runs

The `fk-statement-preservation` unit adds four proof modules, each below 200 lines:
ForeignKeyPlainFrame, ForeignKeyWriteConditions, ForeignKeyStatement and
ForeignKeyRuns. The public statement law follows the actual row engine under its
input, comparison, generated-work and BEFORE-target conditions. Resolved UPDATE
constructs its changed-cell coverage from the assignment list and generated-column
closure; callers supply structural schema/scan conditions, not final row truth.
Plain writes with enforcement off have a separate sufficient condition: the target
is outside all selected FK child/parent reads. The raw execution API is unchanged.

The individual row and combined-atom laws cover `runStatement`, `runSqlFrom`,
`runSql` and `runScriptFrom`. The combined property uses one supplied mapping for
both atoms; compatibility equates it with the catalog-selected comparison. The
run entry condition includes the saved snapshot, and the conditions concern only
reached statements. Success, retained FAIL rows, pending transactions and rollback
therefore use the existing run invariant machinery. Catalog edits are explicitly
excluded from this unit's statement condition and remain open work.

Three new fixtures check 33 reports: all 15 exported proof declarations, nine
statement laws and nine run laws. They apply the public theorem to successful
cascading UPDATE, INSERT, DELETE and UPSERT DO NOTHING; enforced UPSERT DO UPDATE
retains its current undescribed result. They also check actual outside-footprint
partial FAIL, rollback restoration, the necessity of a valid saved snapshot and
an enforcement-off parsed surface INSERT. No interpreter or execution definition
changes. No prediction change is expected from these proof-only additions.

The sequential gate completed with exit 0 on 2026-10-24 (owned process 44603):
`direnv exec . bash build/agent-logs/fk-statement-gates.sh` ran
`timeout 1200 just dev-build` and then the sandboxed focused Nix surface expression
with timeout 1800 and command-local max-jobs=1. The Nix suite passed 14 fixtures,
52 deselected, in 17.29 seconds:
`/nix/store/04dmvlj39cmypsa26ia21rhnskqxsjp1-sqlite-verifier-test-surface-1`.
All 236 axiom reports use only the three standard logical axioms. Logs:
`build/agent-logs/fk-statement-{dev-build,nix-surface}-1.log`. The development build
is diagnostic evidence; the Nix suite is acceptance evidence. Slot 1 returned to
the coordinator after terminal completion. Independent review follows this commit.
The separate `fk-ddl-preservation` workspace holds the next CREATE proofs; the
DROP/ADD COLUMN families, full matrix and part-2 acceptance remain OPEN.

Independent review `20261024T201858Z-ea40e905` checked source commit
`ea40e905be6e484b73cc3358bbcddb3093092e59`: all four proof modules, barrel and
package registration, the three fixtures, test parametrization and status. It
found zero musts and one R19 status should: the top summary still described
completed row/action/trigger invariants as open. The summary now lists the actual
remaining DDL/mapping, matrix, acceptance and corpus work. No source correction
was needed. This accepted statement/run checkpoint is at rest; the DDL unit
continues in its separate workspace.


## CREATE and plain DROP preservation

This proof-only unit adds ForeignKeyCreateFrame, ForeignKeyCreateSelection,
ForeignKeyCreate, ForeignKeyDropSchema and ForeignKeyDdlDrop, each below 200 lines.
CREATE keeps supplied old row comparisons when mappings agree; compatible input
schemas prove that existing parent selections remain stable under append. New
foreign-key declarations need their own located selected parent for the schema
atom, even when the new table has no rows. The separate row-only law remains usable
for a successful empty forward-reference table.

Plain DROP has independent supplied-row and schema-selection transport laws plus
a selected-mapping convenience theorem. Both parent and child positions may move.
The existing row-drop frame now asks its mapping and parent-retention premises only
for surviving child tables. Thus removing a child together with its parent has no
surviving declaration obligation. CatalogValidDrop's existing first-match proof is
strengthened to expose the exact transported lookup as Catalog.findTable_drop_kept;
its sole old consumer now uses that result. The replaced weaker name is removed.
The schema frame reuses this exact lookup and the existing parent-key selector;
it does not implement a new selection algorithm.

Two new surface fixtures apply the public laws to all three CREATE forms, a failing
unique-index creation, forward references, a DROP that moves both table identities,
a removed parent/child family, and successful supporting-index loss that preserves
supplied row truth while breaking schema compatibility. The existing DROP fixture
is adapted to the weaker premise. All new exported theorems, the strengthened
lookup theorem and the changed row frame have axiom reports. The Nix suite enforces
238 reports across 13 fixtures (the prior 203 plus 19 CREATE and 16 DROP reports),
allowing only propext, Classical.choice and Quot.sound.

The sequential gate completed on 2026-10-24 with exit 0.
Command: `direnv exec . bash build/agent-logs/fk-ddl-create-drop-gates.sh`.
It ran `timeout 1200 just dev-build`, then the sandboxed Nix surface expression
with `PYTEST_ADDOPTS="-k independent_foreign_key_atoms"`, timeout 1800 and
command-local max-jobs=1. The development build passed as a local diagnostic.
Nix acceptance: 13 passed, 52 deselected, in 15.65 seconds:
`/nix/store/gxxxsp08l7ncq2hmd1fs9r33ylingvb2-sqlite-verifier-test-surface-1`.
Independent review follows this commit; no task-end acceptance is claimed.

The CREATE/plain-DROP checkpoint started from the accepted engine unit, while
statement/run source `a8bf73ae` was on a separate branch. The integrated unit
below merges those branches and proves the implicit DELETE of enforced DROP.
The earlier plain-DROP theorem itself does not cover that implicit DELETE.
A separate ADD COLUMN execution audit is with the coordinator for an owner scope
decision. No ADD execution definition changed in this unit.

Independent review 20261024T204324Z-135b8338 found zero musts and three shoulds.
The non-CREATE constructors are now listed explicitly in CreatesObject and its
frame proof, so a future constructor requires classification. The top status
clarifies that the accepted DML statement/run unit is on a separate branch.
This acceptance record omits process coordination and external diagnostic claims;
the named Nix result establishes acceptance. The integrated unit below reran
the focused gates with the constructor-only proof correction included.

## Integrated enforced-DROP proof unit

The `fk-enforced-ddl` workspace merges accepted statement checkpoint `a8bf73ae`
and checked CREATE/plain-DROP source `135b8338`. Four conflicts were resolved in
the model barrel, Lake manifest, fixture inventory and this status record, retaining
both branches' formulas and acceptance records. The exhaustive CREATE classification
and all three review corrections from `20261024T204324Z-135b8338` are carried here
with their resolution records. The focused Nix gate now covers the merge and
these corrections together.


Three new proof modules separate the implicit DELETE and catalog removal:
`ForeignKeyDropRows` gives the supplied-mapping NULL-or-retained-parent frame;
`ForeignKeyDropEngine` applies the actual row/action/trigger invariant before
catalog removal and retains partial FAIL states; `ForeignKeyDropCatalog` proves
independent schema transport and the conditional combined law. The combined law
requires retained parents and selected-link transport. Dropping a referenced
parent can preserve only row truth through NULL, while schema compatibility fails.
No execution definition or prediction input changed in this proof unit.

The new `ForeignKeyEnforcedDrop` and `ForeignKeyDropOutcomes` fixtures exercise
populated SET NULL and CASCADE, an AFTER-trigger FAIL that retains child changes
while keeping the parent catalog, NO ACTION rejection, rollback restoration and
separate row/schema outcomes. Their public-law applications use the explicit
comparison, action, BEFORE-trigger and catalog-frame premises. The existing
fixtures retain CREATE, plain DROP, DML, run and mapping-transport coverage.

Nix acceptance on 2026-10-24: the sandboxed surface suite with
`PYTEST_ADDOPTS="-k independent_foreign_key_atoms"` passed 18 fixtures, with 52
other tests deselected, in 20.10 seconds. Its output is
`/nix/store/s5r4vk09sydz5wk93ypa0dzl8g9fwcr6-sqlite-verifier-test-surface-1`.
The fixture driver checks 293 axiom reports and permits only `propext`,
`Classical.choice` and `Quot.sound`. Each fixture has a 90-second subprocess
bound; the Nix invocation has an 1800-second bound. The required development
build was completed before the Nix check, but is not acceptance evidence.

Independent review `20261025T001914Z-dd60f94c` checked this coherent source and
its merge resolutions after reviewer access was restored. It found zero musts
and two shoulds about stale status text; both descriptions are corrected here.
No production source changed after the Nix gate. The source is frozen at this boundary.
The three shoulds from review `20261024T204324Z-135b8338` are recorded as fixed.
The task remains OPEN: ADD COLUMN and the complete DDL/run contract, final matrix,
part-2 full/verdict acceptance and task-end checks still remain.

## ADD COLUMN default decision merged

2026-10-25: the reviewed spec commit `cc10366a` (task, status and ADR 0022 text for
the ADD COLUMN REFERENCES default contract) is merged into this line by a new merge
commit, not a rebase. Conflicts in the ADR, this task and this status were resolved
by keeping both sides' text. Three planning-only files (prediction-source-filter
task/status and query-sources status) keep this line's later DONE or part-1 state,
because the planning line carried older versions. No source changed in the merge.

## Planning-line records carried by the cc10366a merge

These entries come from the planning line that held the ADD COLUMN decision. They
record the original assignment history; the sections above are the current record.

- 2026-10-24: follow-up review `20261024T122324Z-cf7aa9a6` had no findings.
  Assigned part 1 to agent `foreign_key_atoms` in workspace `fk-atoms`, based on
  `cf7aa9a6`. S4 confirmed the FK files and surface database export are disjoint
  from its remaining part 1. Model barrels remain reserved to S4 until a clean
  boundary. Heavy builds are coordinated with S4 and the build-boundary task.
- 2026-10-24: the owner accepted the mapped-NULL engine correction after native
  evidence showed the old helper accepted `(99,NULL)` for the repeated `(a,a)`
  parent key and omitted its pragma violation. The revised task corrects the
  shared helper first, updates default mappings/proofs, and requires native
  regressions. Selected child columns determine NULL exemption; missing or
  mismatched targets retain the declaration-column fallback. The working API
  split is preserved in `sqlite-verifier-fk-atoms`. Agent `text_build_boundaries`
  has resumed it and adapted the helper, mapping proofs and native cases;
  model/Nix checks remain. Native-only replay is diagnostic, not acceptance.
- 2026-10-24: pinned native replay found an enforced parent replacement that
  leaves an orphan because child-scan and parent-lookup affinities differ.
  Added the necessity example and explicit comparison-consistency premise to
  the existing conditional preservation contract. This is within the accepted
  schema/mapping/effect conditions, not another engine change or an assumed
  final atom. The owner was informed; part 1 and independent work continue.
- The accepted action scope is carried at `1a10a3c8`, with clean follow-up
  review `20261024T152329Z-01a02bef`. Resolution and execution share the selected
  child projection. Trigger preparation reads assigned columns; generated
  dependencies feed FK constraint checks. The Nix native gate passed all 35
  differential/kernel cases at
  `/nix/store/mhvsqdz6wnx66s0rr80a12yp5xam6hif-sqlite-verifier-test-model-1`.
  Surface/mutant Nix gates and part-1 full/verdict remain open. Part 2's global
  counter invariant and statement/run preservation are still implementation work.

## ADD COLUMN execution correction (part 2, unit 1)

2026-10-25. Native SQLite 3.51.0 refuses `ALTER TABLE ... ADD COLUMN` of a
`REFERENCES` column with a non-NULL default when foreign keys are on and the table has
rows, even when the parent row exists. The model did not refuse it. This unit adds the
refusal; the preservation laws for ADD COLUMN are the next unit.

- Resolution marks the statement: `Resolved.Statement.addColumn` has a third field
  `refusesPopulated`, true when enforcement is on, the column has a foreign key and its
  written default (the last DEFAULT) is not a literal NULL (`literalNullDefault`).
- `step` checks it first, before the NOT NULL, CHECK and clock-default checks, and gives the
  new `ExecutionError.referenceColumnDefault` (primary code 1, database unchanged). An
  empty table, enforcement off and a NULL or absent default are accepted as before.
  The same error is added to messages, output names, failing constraints, the conformance
  case reader and the `DbDiagnostics` reader.
- Laws that mention ADD COLUMN take the new field. The refused branch keeps the database, so
  keys-unique, row-local, extension and run-step laws gain one trivial case.
- Finding: native accepts a bare `DEFAULT +NULL` as a NULL default. It refuses `-NULL`,
  `(+NULL)` and `(1)`. The model leaves `+NULL`, `-NULL` and parenthesized defaults
  unsupported, so `literalNullDefault` is equal to the native rule but the unsupported forms
  never reach it. The ADR and task text say this.
- Tests: `tests/add_column_references_test.py` compares the model with native for the
  default, empty-table, NULL, last-default, enforcement-off, error-precedence and
  unchanged-state controls, and checks that the unsupported forms are outside the model.
  `tests/surface/DbBangChecks.lean` checks the message.
- Mutants: `conformance/add_reference_mutants.py` (5 mutants, all killed), authored cases in
  `conformance/authored_add_references.py`.
- Predictions: all 53 prediction files are identical before and after (0 differences). The
  corpus v54 judge change must add the native regression cases for ADD COLUMN REFERENCES
  defaults; this line does not edit judge, corpus or lock files.
- Nix results (focused groups):
  - model `add_column_references or add_column_defaults or foreign_key_atom_execution`:
    43 passed, `/nix/store/0v8fyn3nf94plfx1vjbdx1xdkqzna50q-sqlite-verifier-test-model-1`.
  - surface `db_bang_messages or independent_foreign_key_atoms`: 19 passed,
    `/nix/store/j9qrv7kfy0xamakgqqxk5jal4cia2mdj-sqlite-verifier-test-surface-1`.
  - mutants `add_reference or foreign_key`: 2 passed,
    `/nix/store/0gp4p5q78rgz7h05w7mziqwqzxvbzfn8-sqlite-verifier-test-mutants-1`.
- Review `20261025T063516Z-43e19791` found four musts (R5 catch-all patterns, R2 plain-words
  statements without the refusal flag, R12 file length, R19 stale status summary). The refactor
  commit fixes all four: `literalNullDefault` lists every constraint constructor, the ADD COLUMN
  laws say that they hold for either value of the flag, `Execution.lean` is 199 lines, and the
  summary above is corrected. The first Nix run of the refactor failed: replacing the final
  `match` of `literalNullDefault` with `==` on `Syntax.Expr` stopped `decide` in the authored
  cases from reducing (a `sorryAx` axiom report). The refactor keeps the pattern match there.
  Nix results of the refactor (same focused groups): model 43 passed,
  `/nix/store/5daqjw19jahx1l6h5qgvgfwlal1qnm3a-sqlite-verifier-test-model-1`; surface 19 passed,
  `/nix/store/jdb7jnqy243n75d6m9q3gk76ywwnwh2v-sqlite-verifier-test-surface-1`; mutants 2 passed,
  `/nix/store/fcbqflf4kaivva1wwj36visiy6m9j92z-sqlite-verifier-test-mutants-1`.
- Review `20261025T070529Z-b520f373` of that refactor found one must (R5): the final `match` of
  `literalNullDefault` still ended in `some _`. The second refactor lists every `Syntax.Expr`
  constructor, with the helper `isNullKeyword` for the operand of the unary plus, so a new
  expression form needs a decision. The mutant `add_reference_null_refused` changes the new text.
  Nix results (the same focused groups; the working tree also held the unit 2 files, which the
  groups do not exercise): model 43 passed,
  `/nix/store/fibp443s8gb65g2gd6yq28fayxlgqsj7-sqlite-verifier-test-model-1`; surface 20 passed,
  `/nix/store/x3ffc4dg3x15ab5sjs2b38z5nc4jhap1-sqlite-verifier-test-surface-1`; mutants 2 passed,
  `/nix/store/7z3if3ip2c7laf40mdlnlvahgjq78502-sqlite-verifier-test-mutants-1`.
- Remaining in part 2: ADD COLUMN preservation laws and fixtures, the unified DDL run contract,
  RESTRICT / SET DEFAULT / deferred coverage with the final matrix, then part-2 full and verdict.
