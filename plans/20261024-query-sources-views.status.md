# Status: query-source views

Created 2026-10-24. Part 3 OPEN; the overall query-source task remains OPEN.
Task: [queries as sources](20261024-query-sources.task.md).
Main status: [accepted parts and publication](20261024-query-sources.status.md).
Specs: ADR 0019 D5/slice 4 and ADR 0017 S6.

## Foundation: declared-type origins

The foundation retains the declared-type origin of each resolved result column
separately from its expression affinity and collation. SQLite's `columnTypeImpl`
follows physical columns, derived columns and scalar subqueries; a compound
follows its right-most term. CAST, COLLATE, unary plus and a full-join coalesce
have no declared-column origin. RIGHT JOIN's merged output follows the right
column. This is metadata needed by view column descriptions, not view DDL.

The existing source resolver and scalar shapes carry that metadata. No evaluator,
CatalogEntry constructor, SQL form or FK definition changes in this unit.
The normalization unit below handles native evidence that distinguishes
SQLite's FLEXNUM metadata from ordinary NUMERIC, including through nested views.
Origins alone do not approximate those types with a copied declaration.

Kernel examples cover all columns of a star, absent declarations, expression
wrappers, INTEGER/REAL compounds, nested derived columns, LEFT/RIGHT/FULL merged
outputs, scalar subqueries and the complete indexed resolver. The existing
physical-column query proofs carry the additional origin in their shape
premises; their conclusions and the S4 physical-table premises are unchanged.

The descendant also carries the published PR #248 CTE acceptance/status text and
ADR implementation paragraph from `e3d6aa388eeb070b94cdcf34a474f79f692d3c12`.
The full publication ancestry will be merged at a later clean boundary.
The focused Nix surface check passed all 17 selected fixtures (55 deselected)
at `/nix/store/zqx7vb0nvvhp89fvx34ncpcfjh2wy2g4-sqlite-verifier-test-view-column-origins-1`.
It includes the physical-column IN claims, source/CTE consumers and the complete
balance success proof. The model package build checks the origin kernel examples.
Nix predictions at
`/nix/store/kdphp0hd50xm2cp21b8xkir65cjhylwh-sqlite-verifier-predictions`
match the accepted CTE baseline
`/nix/store/wbpwn1x38fyn3l0g00wg5m011n6ajwq4-sqlite-verifier-predictions`
byte-for-byte: all 53 files and 7,372 cases, with zero changed records.
The exact comparison is retained in
`build/agent-logs/view-column-origin-prediction-changes.json`.
Independent review `20261024T203741Z-86e15af9` found zero musts and two shoulds:
enumerate the remaining star-operand constructors and wrap the compound-shape
docstring. Both are corrected in the normalization descendant below.

## Foundation: normalized source declarations

This unit computes normalized declarations separately from origins and
expression affinities. It preserves a declared spelling when affinity agrees;
otherwise it selects SQLite's INT, REAL, TEXT, BLOB or NUM spelling. Expressions
without affinity have no declaration. A physical untyped column has BLOB
affinity and therefore normalizes to BLOB.

Compound declarations use the left-most origin and the effective source
affinity. Expression origins still follow the right-most term. A metadata flag
retains SQLite's FLEXNUM distinction through derived sources, scalar shapes,
COLLATE and stars. A first-term CAST with a retained numeric compound affinity
sets that flag; a text conflict that changes affinity to BLOB clears it.
The numeric Value operations, comparison affinities and evaluator are unchanged.

Kernel examples distinguish direct INTEGER/REAL compounds from enclosing
queries, original declarations from canonical names, wrappers and untyped
columns, and nested FLEXNUM from ordinary NUMERIC despite their equal NUM
spelling. Existing scalar-query proof premises for physical tables remain the
same: a small law proves their expressions cannot inherit a FLEXNUM flag when
the scope has no resolved subqueries.

The focused Nix check passed all 17 selected fixtures (55 deselected) in 44.53
seconds, including the complete balance proof and physical-column IN claims:
`/nix/store/yy0xf2n1yrg9assy7y31bfda0v6ign9q-sqlite-verifier-test-view-column-types-1`.
Its model dependency checks the new normalization examples in the kernel.
Nix predictions at
`/nix/store/50ck3gadmqmjl6yp9s4mz03f3da1bim9-sqlite-verifier-predictions`
match the accepted CTE baseline above byte-for-byte: all 53 files and 7,372
cases, with zero changed records. The exact comparison and Nix logs are retained
under `build/agent-logs/view-column-types/`. Independent review
`20261024T210304Z-858e0a2b` found zero musts and zero shoulds. The checked source
is `858e0a2b14c0457c378edd7b2bd9e85af26ed5c0`.

## Catalog integration base

The catalog workspace merges the reviewed metadata head `c0e288b5` with published
PR #248, `e3d6aa38`. Its production packages are byte-identical to `c0e288b5`;
the published parent supplies the S6 and proof-cost prototype test registrations.
The two query-source status conflicts retain the newer acceptance records and
the retained S4 archive paths. The Nix foundation evidence above is unchanged.
No catalog or evaluator behavior changes in this integration commit.
Independent review `20261024T210803Z-63bcea9d` found no findings.

## Foundation: unresolved view catalog

The catalog now stores a view's written query, optional column names and indexed
expression subqueries. It retains names through catalog drops. A view occupies
the shared table/index namespace and has no stored rows. Catalog validity permits
missing references and cycles in the unresolved definition. The generic append
and drop laws cover the new catalog entry.

This is an interim catalog unit. CREATE/DROP VIEW syntax and query expansion are
not implemented yet. A manually supplied view is explicitly unmodeled at source,
write, trigger, index, ADD COLUMN, DROP TABLE and table-info boundaries that need
the later view handling. These paths do not invent a missing-table error or an
empty metadata result. Foreign-key listing and check pragmas use the catalog
object without expanding its SELECT. An existing view produces the native
view-name collision for CREATE TABLE and shared-name collision for CREATE INDEX.

The FK parent lookup distinguishes an absent name from an existing view: the
latter is a position-bearing mismatch, even when the view body cannot resolve.
The parent-schema frame therefore preserves the optional view position when no
physical parent exists; view bodies remain unrestricted. The selected mapping,
NULL, affinity, collation and action formulas are unchanged. The coordinated FK
proof closure adds only the new non-table cases. The exact retained-table lookup
law in `CatalogValidDrop` and its caller are carried from checked FK source
`135b8338948d9b3737c236f765e6fb2c841a6131`.

Missing-source laws now require view absence. Pragma-function laws require that
neither a table nor a view shadows the function. The maintained balance fixture
handles both shadowing cases while retaining the physical-ledger premise and all
SQL/data guards. The private guide mirror is deferred to the final installed
integration artifact; no private content is carried here.

`ClaimsViewCatalog.lean` checks manually supplied definitions, catalog positions,
row shape, name collisions, FK mismatch, conservative expansion boundaries and
pragma behavior through the public predicates. The selected surface suite also
checks the complete balance proof, arbitrary callback consumers and all nine FK
fixtures. The conformance loader and table comparator keep view storage empty;
their existing observations still describe physical tables, not view definitions.

The focused Nix check passed all 28 selected cases, with 53 deselected, in 57.17
seconds:
`/nix/store/lvbs6wdb1ck7bpxy746plv8a5h1q7xxl-sqlite-verifier-test-view-catalog-1`.
Nix predictions at
`/nix/store/d0szrxzshhfncprggija4qdjhps7xczq-sqlite-verifier-predictions`
are byte-identical to the accepted CTE baseline: all 53 files and 7,372 cases,
zero changed records. The logs and comparison are retained under
`build/agent-logs/view-catalog/`. Full view-part acceptance remains pending;
this checked foundation does not complete part 3.

Review `20261024T214402Z-59dc5215` found no findings but disclosed incomplete
file coverage. Supplementary review `20261024T214759Z-59dc5215` inspected all
77 changed files and found three stale mutation anchors. The follow-up preserves
the new view branches while restoring the existing CREATE TABLE, missing-table
ADD COLUMN and DROP TABLE IF EXISTS mutations. A static audit also found two
stale derived-column affinity/collation anchors from the metadata foundation;
the same follow-up restores those mutations without changing their targets.
All five named Nix mutant checks passed, one selected mutant per invocation.
Each retained the existing unchanged-model agreement and mutant-kill assertions.
The disposable selection changes the existing dictionary in place, including the
resolver runner's captured default; it adds no permanent runner or test.

- `no_table_exists`: `/nix/store/ly18lnjdlqqbzwgwf2av057hyhlab084-sqlite-verifier-test-view-catalog-mutant-no_table_exists-1`.
- `no_such_table`: `/nix/store/2sqxk6736i6v4lc8g0ahwq6zsmji8n4p-sqlite-verifier-test-view-catalog-mutant-no_such_table-1`.
- `if_exists_reports_missing`: `/nix/store/p922y6qblmf5pwdsflvy2fvyx43ap74x-sqlite-verifier-test-view-catalog-mutant-if_exists_reports_missing-1`.
- `source_affinity_lost`: `/nix/store/ww4csy3i19viqg04nj0jbvv6z505crb6-sqlite-verifier-test-view-catalog-mutant-source_affinity_lost-1`.
- `source_collation_lost`: `/nix/store/5wslqf8vgvzrkbhrfkrkb0h3b4dzjma9-sqlite-verifier-test-view-catalog-mutant-source_collation_lost-1`.

Logs and the exact disposable selection are retained under
`build/agent-logs/view-catalog/`. No model or proof definition changes in this repair.

Repair source `a890097fe76f92529517393bd5ba904f1a8853d9` passed independent
review `20261024T215844Z-a890097f` with zero must and zero should findings.
The catalog foundation and its five mutation repairs are now checked and reviewed.

## Stored source expansion: focused checks and review passed

The source workspace preserves checked expansion snapshot `700bd0d2` and merges
complete S6/native source `5bc323f0` without rewriting either ancestor. Stored
views enter the existing indexed query resolver. Ordinary caller names and CTEs
are hidden while trigger NEW/OLD names retain their actual cell offsets. The
same stored definition is checked in ordinary, scalar, derived and trigger
contexts. Cycles, missing references, explicit column counts and invalid function
calls retain their preparation errors. The source evaluator honors the existing
outer-cell width while preserving the shared clock and counters.

The merge adds only mechanical S5 view cases: views have empty sampled storage,
and automatic replay refuses a catalog whose view DDL it cannot reconstruct.
The explicit replay primitive remains available. S5 owns its subsequent sampler
refactor; these cases remain frozen for that later coordinated integration.

The initial focused Nix attempt, session `24597`, passed seven fixtures and
failed the new seeded-sampling assertion. The pinned random generator uses a
private partial function that does not reduce in the kernel; the assertion did
not establish a false catalog result. The fixture-only correction uses the
existing executable generator observation, then separately kernel-checks the
reified database validity. Pure empty-storage and replay facts still have kernel
proofs. No sampler, RNG or model definition changed to accommodate the fixture.

Frozen corrected source `e383c4f4d29153a040580c90f1d5f15be2c173a9` passed all
eight selected Nix cases, with 82 deselected, in 45.15 seconds:
`/nix/store/cj5vhkv8xxk9iqz7q4yal2yi7hk1c0ry-sqlite-verifier-test-view-expansion-integration-1`.
The cases include three stored-view fixtures, the catalog boundary, both complete
S4 guide success fixtures, and derived-source/CTE consumers. Nix predictions at
`/nix/store/lnz7y254m8cvgkz2fv9zw4cqcq3898i5-sqlite-verifier-predictions`
match the accepted integrated baseline
`/nix/store/v8f8kr8g9i0labdhf6021rpwnp47z939-sqlite-verifier-predictions`
byte-for-byte: 53 files, 7,372 cases and no changed file. Logs and the exact
comparison remain in this workspace's `build/agent-logs/` as
`view-integration-focused.log`, `view-integration-focused-retry.log`,
`view-integration-predictions.log` and `view-integration-prediction-comparison.json`.

Independent review `20261025T001433Z-694d0790` checked frozen source
`694d0790117126afd07fa8cb9add72065988c6bb` and found zero musts and zero shoulds.
These focused checks do not complete part 3 or replace its post-review full/verdict and
task-end acceptance. The existing result-alias limitation is recorded separately;
this unit makes no unrelated resolver or mutant-harness correction.

## Remaining view scope

CREATE VIEW, complete pragma metadata, write errors and the remaining preservation
closure remain OPEN under the existing task. DROP VIEW is checked in the unit below.
Stored-source expansion has
the focused checks and independent review above. FK proof leaves are
coordinated with their owner before mechanical view-case extensions. Frozen v53
remains unpublished and mutable in the separate evidence workspace. No corpus,
claim or judge-lock file changes in the foundation.

## Resumed view completion

The implementation workspace merges the reviewed view boundary `7e458081` with
published mutant repair `fe169099` (PR #251), without rewriting either history.
The merge has no conflicts and preserves every production package from the view
parent. It carries the published grouped-edit harness and changes exactly three
BEFORE anchors to the existing view source: both star guards use `namesVisible`,
and the correlated source uses `outer.take query.outer`. The two changed tables
are byte-identical to checked integration `d280c408`; native targets, baseline
agreement and kill assertions are unchanged. No S5 frontend descendant is carried.

The source and approved shell comparisons are recorded in
`build/agent-logs/view-repair-integration.json`. The harness, full guard inventory
and test-ownership checks are local diagnostics for this merge, not Nix acceptance.
Model-edit prediction comparisons will use the accepted `lnz7y254` output above.
The remaining CREATE/DROP VIEW, pragma metadata, write errors and preservation
scope stays OPEN under the existing task. `text_build_boundaries` owns this work;
the migration worker retains its separate normalized-field proof leaves.

Integration `c3e4346f579d9bc34430b814b0e7c63897e584f6` has clean independent
review `20261025T013259Z-c3e4346f` (0 must, 0 should). Its focused Nix evidence
reuses checked `d280c408` under the coordinator's exact-input rule. Model, text
and conformance sources are byte-identical. Instantiating the same focused
selectors gives the exact already-realized derivations; no build was needed:

- Harness: `qdzcv4580j47nvi4dp2iqrw8sms7xhnr`, **12 passed**, at
  `/nix/store/mvcmxxkr5nnlaxdmid9zrg97pkzj08fp-sqlite-verifier-test-frontend-anchor-harness-1`.
- Fromless/subquery groups and guard inventory: `z156psnyk8r8ijgrwb5j3rsll8xs9pwr`,
  **52 passed**, at
  `/nix/store/9v0kp2s6qbrhv6ksg52wf1simvabdccb-sqlite-verifier-test-frontend-anchor-mutants-1`.
  All four fromless and four subquery faults retain baseline agreement and kill
  assertions. The 50 guard-inventory cases pass.

`build/agent-logs/view-repair-reused-nix.json` records the exact derivation/output
identities and checked XML counts. The adjacent selector files and evaluation
logs make the comparison reproducible. This completes the harness integration;
the view feature and its full acceptance remain OPEN.


## DROP VIEW: focused checks passed

The syntax and text layers now accept DROP VIEW and DROP VIEW IF EXISTS. The
resolver uses the existing resolved drop execution. It removes the view's catalog
position and empty storage without resolving its definition. Existing physical
rows remain intact, later catalog positions shift, and rollback restores the
original catalog and rows. The public runner's generic validity proof covers the
new syntax constructor; new resolution laws establish the catalog step, resulting
catalog, dependency closure and schema link.

DROP VIEW against a table and DROP TABLE against a view produce SQLite's
wrong-kind messages, including with IF EXISTS and with the declared object's
spelling. Missing names, indexes and protected schema tables retain native error
precedence. A valid catalog requires every trigger to name a physical table
(`CatalogObject.supported`); triggers attached to views are not admitted, and
INSTEAD OF remains excluded. Removing only the view position is correct within
that scope. No foreign-key formula or file changes in this unit.

The first Nix surface attempt on `d6e049f9` passed 24 of 25 selected cases,
including the new DROP VIEW fixture's nine axiom-audited kernel claims and eleven
native message comparisons. Its only failure was the existing trigger fixture's
exhaustive helper, which needed the new syntax case. The correction adds only
that non-body case and clarifies the Python test documentation. Production
package sources are identical between that attempt and corrected `2a3f14a9`.
The retained first-attempt log is `build/agent-logs/view-drop-surface.log`.
Per coordinator approval, passed unrelated fixtures were not repeated.

Focused Nix evidence:

- Corrected trigger fixture: **1 passed**, 90 deselected, at
  `/nix/store/p4d5asbk3a1dp8w79vh7xfdw69wb0g5w-sqlite-verifier-test-view-drop-surface-retry-1`.
- DROP syntax and schema-qualification boundaries: **4 passed**, 251 deselected,
  at `/nix/store/i7289fwx5vkxfm515w7i06q17rnyykd5-sqlite-verifier-test-view-drop-model-1`.
- Existing named DROP mutant group: **1 passed**, 9 deselected, at
  `/nix/store/47kn6iiinwh59di6ix5gm074vqkmshyl-sqlite-verifier-test-view-drop-mutants-1`.
  All three faults retain unchanged-model agreement and mutant-kill assertions.
  The IF EXISTS source anchor follows the new nested match; its fault and target
  are unchanged.

Predictions at
`/nix/store/xi0rgkd2nfxfilb63wygqxdxswjbd7kv-sqlite-verifier-predictions`
contain the same 53 files and 7,372 cases as accepted `lnz7y254`. All output and
modeled-status fields are unchanged. Exactly 387 records in corpus v1–v5 differ
only in the unsupported-statement reason, which adds DROP VIEW to the supported
statement list; 48 files are byte-identical. The exact per-record comparison and
verified single replacement are in
`build/agent-logs/view-drop-prediction-comparison.json`. This is no claimed
corpus agreement gain. No corpus, claim or judge-lock file changes.

Commands, selectors and logs are `build/agent-logs/view-drop-*`. The package dev
build and development verdict are required local diagnostics, not acceptance
citations. Independent review `20261025T022201Z-7ebea057` checked source
`7ebea057f9ada581ad951a15efaf3ad045219553` and found zero musts and zero shoulds.
The reviewer reported reading the diff and changed files, with no coverage limitation.
CREATE VIEW and the remaining view scope above still require their implementation and full
part-3 acceptance; neither this unit nor its focused checks completes the task.

## CREATE VIEW and view observation: checked

CREATE VIEW stores the resolved view body, and the predicted catalog and native
observation list views like tables. A view row is an observation, never a stored row.
`observeView` resolves `SELECT * FROM view` with `resolveSelectDetails` and runs the
result with `resolvedStepOutput`; there is no second query interpreter. An unreadable
view keeps its prepare or step error. A clock-reading view without a known clock is
unmodeled. `abs(INT64_MIN)` inside a view stays the existing fallible-source restriction.

Two model gaps that native comparison exposed are fixed in this unit, because the
view cases need them. They are not view features:

- `x IN ()` now drops its operand as the SQLite parser does (translator,
  `Translation/Forms.lean`), so an unresolved name or subquery there is no error.
- A result column alias in an ON condition is now an `alias-in-expression`
  restriction, as it is in WHERE. Native resolves it; the model did not.

Nix evidence (all on this source tree):

- Focused harness (observation, predict, pass, counter tests): **41 passed**, 216
  deselected, `/nix/store/micf7fh3a5i8pb8gf31v8xav88hgwlnj-sqlite-verifier-test-view-observation-harness-1`.
- CREATE/view/FK/schema/layer surface cases: **26 passed**, 66 deselected,
  `/nix/store/mndkwxlxn5fb6plyalry5qmpbg64s5yk-sqlite-verifier-test-view-create-surface-1`.
- Syntax cases: **6 passed**, 255 deselected,
  `/nix/store/03cqhxl3xmifns5sfnln3b0zwyn1lskb-sqlite-verifier-test-view-create-model-1`.
- Predictions `/nix/store/6ywc5znd40bmhqxa85vzxpazdn6r4w27-sqlite-verifier-predictions`
  against the accepted baseline `xi0rgkd2nfxfilb63wygqxdxswjbd7kv`: 53 files, 7,372
  cases, 48 files byte-identical, and every previously predicted record unchanged.
  402 records differ: 97 change from unsupported to predicted, 267 change only the
  unsupported-statement reason (CREATE VIEW is now a supported statement) and 38 change
  the reason and the restriction. The record is `build/agent-logs/view-observation-prediction-comparison.json`.
- Verdict `/nix/store/ji3bwji6ln6p3lwp9qbli54w12capajv-sqlite-verifier-verdict`: no
  DISAGREE and no HARNESS_ERROR; AGREE 4,962, MODEL_UNSUPPORTED 2,410 (7,372 cases).
  Of the 97 new predictions, **93 AGREE** and 4 are MODEL_UNSUPPORTED because the
  prediction declares itself out of scope (`altertab2-8.1` and `altertab2-8.3`, in corpus
  v4 and v5). Before the observer, 100 of 101 new predictions DISAGREED. Eight of
  those 101 are now restrictions (seven `alias-in-expression`, one `rowid-name`), and
  four predictions are new, so 97 remain. The agreement gain over the accepted
  baseline (4,869) is 93.
- `lake build` of `packages/verifier-conformance` and `packages/belay` both exit 0
  (local diagnostics, as the rules require; not cited as acceptance).

Judge-side gaps, not changed here (judge files are locked): the recorder throws on a
CREATE VIEW whose body names a missing table or is cyclic, and `judge.records.subject_input`
does not forward `setupClockUnixMilliseconds`.

Logs: `build/agent-logs/view-observation-*`. The remaining view scope (PRAGMA
table_info on views, broken-view errors, unsafe pragma use in view bodies, write errors,
catalog closure) stays OPEN.
