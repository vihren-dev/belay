# Status: S6 migration views and patterns

Created 2026-10-24. Status: OPEN. Assigned for implementation.
Task: [task file](20261024-s6-migration-patterns.task.md).
Specs: ADR17 S6 and the accepted explicit observation-view decision.

## Scope and dependencies

The owner accepted a migration observation view instead of a quiet action that
changes ordinary execution or equivalence. Query preservation/translation use
an explicit weaker comparison; commutation compares the projected trace and
complete non-trace context. Failures, return values, counters and clock effects
remain real. The positive expansion application theorem belongs to S8 scoped
simulation because its write order changes total_changes.

The production execution prerequisite is present at immutable `5bc323f0`, the
base of this implementation workspace. Final table-rebuild and FK work is still
needed for the cascade example. Existing reviewed native diagnostics inform
these contracts but are not implementation acceptance. The descriptors,
comparison/pattern primitives, composition/frame laws, named commutation laws
and pattern frontend have focused evidence and clean independent reviews below.
Their first acceptance part passed post-review full/verdict checks on 2026-10-25.
Universal examples, private-guide corrections, the second acceptance part and
task-end checks remain required.

## Progress

- 2026-10-24: specified view erasure/projection, exact pattern domains, contextual
  comparison laws and universal example acceptance. Review
  20261024T152701Z-56b9f410 found no musts or shoulds. Implementation was then
  unassigned; the assignment entry below supersedes this historical state.
- 2026-10-24: readiness audit against complete execution source `5bc323f0`
  found the first acceptance part can start independently of the later FK,
  rebuild and assertion-notation work. Reuse `Sql.runFrom`, `Sql.Branch`, its
  actual-run and bind laws, `ExecutionContext.finish`, `SucceedsFrom`,
  `EquivAt` and `ObservationEquivAt`. The compared trace can be projected;
  execution continuations must still receive their selected raw or concrete
  output. The reached index uses the original trace length, not the projected
  length. Preserve values, errors and stopped outcomes.
  Use `SucceedsFrom` for migration success at the original context; `andOk`
  also constrains the prior trace and would narrow that domain. Query admission
  uses `Script.isQuery` and `Syntax.Statement.readsOnly`; the program `query`
  helper checks statement count and is not a read-only premise. New view and
  pattern modules can own separate fixtures and narrow manifest additions.
  Implementation was not yet assigned at this audit; the next entry supersedes
  that historical state. The whole task remains open.
- 2026-10-24: assigned the reviewed task to `s6_prerequisite_audit` in
  `sqlite-verifier-s6-migration-patterns`, based on immutable `5bc323f0`.
  The task text is byte-identical to reviewed source `56b9f410`.
  The first unit covers execution-view descriptors and projection laws with
  installed kernel fixtures. Reserve new `ExecutionView*` and
  `MigrationPattern*` modules and their narrow export/test registrations.
  Existing execution semantics, S5 search/replay, S7 file helpers and model
  view work keep their current owners. The worker may prepare this source
  while its frozen view gate runs, but may not start another heavy process.
  Freeze the first checked source unit for independent review; the reviewer
  login remains an external prerequisite. Later examples and whole-task
  acceptance remain required.

## First unit: execution descriptors and projection

The workspace carries the exact task and assignment record from planning
`e43a891d`, plus clean review `20261024T152701Z-56b9f410`. The accepted ADR17
observation-view and S8 full-context/scoped-context paragraphs are copied from
that planning revision. They synchronize accepted decisions; this unit adds no
new product scope or S8 implementation.

Four new public leaves provide the descriptor, projection and laws:

- `ExecutionView`: an indexed witness for the original `Sql` program, uniform
  identity/quiet helpers, result-dependent bind and interpreter erasure.
- `ExecutionViewProjection`: projection follows each recorded raw or concrete
  continuation output. It preserves errors and stops, leaves return values
  unchanged, and finishes the raw run before replacing only its visible trace.
- `ExecutionViewLaws`: identity, ordered failure retention and exact return,
  clock, raw index, connection and prefix-trace properties.
- `ExecutionViewBind`: stopped-prefix and returning-prefix concatenation laws,
  indexed by the existing execution branches, and full-context concatenation.

These definitions execute no SQL and change no existing interpreter or branch
meaning. The existing model, S5 and S7 definitions are unchanged. A descriptor
supplies a continuation view for every possible output; successful outputs with
equal values do not determine segment boundaries. The full reached index counts
the original trace length, even when every successful output is hidden.

The checked implementation is carried by commit
`504b819bbcd70e5802947b18db197bb33dd69498`. Its production/test files are unchanged
from frozen source `95363cc66c75347338d56292e82a7436ee8d4ee9`, which passed the focused
installed Nix check: two groups, 85 deselected, 13.56 seconds, at
`/nix/store/3f2nwr14gs5wz0j4q1vhp3ix3xa50ayh-sqlite-verifier-test-execution-views-1`.
The installed surface is
`/nix/store/5a7xzb629mzc773y1h6miv7xhdfqhk4y-belay-0.1.0`.
The new fixture checks 27 proof-dependency reports; the existing execution group
checks 101. Every report uses only the permitted ordinary logical axioms.
The fixture includes empty/multiple steps, duplicate outputs, result-dependent
raw/concrete choices, returned migration outputs, errors followed by writes,
stops inside/outside the migration, transaction snapshots, counters and advancing
statement clocks. Generic branch laws cover every permitted prefix branch.

The first focused attempt failed in the new fixture on syntax/indexing errors;
the existing execution group passed. The correction changes only the fixture
and its report parser, which now also counts axiom-free reports. Logs are retained
under `build/agent-logs/` as `execution-views-focused.log` and
`execution-views-focused-retry.log`. The disposable Nix selector uses the existing
surface suite and unchanged timeouts; it adds no test runner.

R3/R19 self-review checked the public formulas against their plain-words
contracts and the exact existing branch/finish APIs. After the owner's login
refresh, independent review `20261025T001307Z-504b819b` found zero musts and two
status-only shoulds. Both are fixed here: historical assignment wording and the
link from the checked source to its carrying commit. The review found no source,
task, ADR or fixture issues. The descriptor implementation remains unchanged.
At that boundary, projected comparisons, migration domains/patterns, their laws
and later examples were unfinished. The subsequent units below advance those
requirements; the acceptance part remains OPEN. No full/verdict
or task-end acceptance is claimed by this focused check.

## Second unit: projected comparisons and pattern primitives

This checked source unit adds six leaves: weak/full view comparisons, their
elementary equivalence laws and identity bridges, original-context migration
domains and comparison meanings, fresh query/application helpers, and pure
migration/domain-restriction/vacuity laws. Both comparison relations retain
actual-run equality separately from all raw/concrete branch observations. Full
comparison retains the complete connection, clock and raw next index. Pattern
domains use original-context SucceedsFrom without requiring an OK prior trace
or success after the application moves. Both commutation orders return the
application's value; fresh helpers quantify every admitted bundled database and
complete environment, and query helpers require single read-only scripts.

Three new installed fixtures cover identity bridges, weak/full/strong
distinctions, raw/concrete branch sets with unequal actual results, moved failure,
original-failure vacuity, returned application values and counter effects. The
production interpreter and model definitions are unchanged.

Commit `838aa29e3057c196187b5c5964cab6b890e0b633` carries this checked unit.
Its production, fixture and test-registration files are unchanged from
frozen source `bce35aae4294161738924cb73031d49871cd7bce`, which passed the installed Nix
check at `/nix/store/4ngn8pikwbsql2fqflbvmgc7gz6crxm9-sqlite-verifier-test-migration-patterns-1`:
three groups, 85 deselected, 17.97 seconds. The installed surface is
`/nix/store/g9p5fxs570xbh8qijbwvc54ilafzmra3-belay-0.1.0`. The new fixtures audit
32 proof-dependency reports; the existing view and execution fixtures audit
27 and 101 respectively. All 160 use only permitted ordinary logical axioms.
The disposable selector retains the existing surface suite and timeouts.
Log: `build/agent-logs/migration-patterns-focused.log`.

The mandatory development build and targeted fixture diagnostics completed
before that Nix check. Fixture-only corrections supplied direct finite-choice
proofs, introduced a let-bound program before its comparison assumption, and
escaped a checked-doc identifier; no production formula changed after the first
build. A preliminary disposable local runtime lacked dependency-library links;
the normal installed Nix runtime required no repair. Diagnostic logs remain in
`build/agent-logs/`; only the Nix result above is acceptance evidence.

R3/R19 self-review checked the actual/branch separation, exact identity bridges,
original-context domain, application return values, fresh quantification and
read-only admission. Independent review `20261025T002522Z-838aa29e` found zero
musts and one status-only should: identify the commit carrying the checked
source. That provenance is recorded above, and the finding is resolved without
changing production or test files. Composition/frame bridges were still pending
at that boundary and are supplied by the next unit. Notation, universal guide
examples and whole-task checks remain required; neither acceptance part is complete.

## Third unit: composition and sufficient full-context frames

Commit `c398676a6446820c96901e54cb69c80837e5b9ca` (Jujutsu change
`sryuxykuqtvllozsqtwoprummxowquun`) carries this unit. Its production, fixture and
registration files are unchanged from frozen checked source
`b3125854f4278c7b9fd633c64ebd3934f6f99190`. This unit adds nine proof leaves,
without changing any existing execution, comparison or domain definition.

Full projected bind composition uses existing raw `Sql.ReturnsIn` premises.
The proof transports a tail comparison across prior traces only after checking
it at the left raw reached context; it never transports the trace-sensitive
precondition. A separate weak rule replaces tails after the same raw prefix.
Success of a combined migration supplies both component success obligations
through a proved bind-success equivalence. Translation and preservation compose
when the first migration preserves the second pattern's explicit raw domain.

The sufficient translation-to-full-commutation bridge requires success of the
migration after every returning application branch, equality of complete
connections for matching observed branches, and equality of their raw step
counts. These are explicit theorem premises, not changes to the original
migration-success domain. Connection equality includes counters, settings,
snapshots, stored clock assignments and the catalogs used for resolution.

Frozen source passed the installed Nix check at
`/nix/store/x6cp3k3a7vlx9z8k0jrhdzcllm4bls22-sqlite-verifier-test-migration-composition-1`:
three groups, 85 deselected, 24.23 seconds. The installed surface is
`/nix/store/nylj3627c7ygx75jih41hymqxjxpqfym-belay-0.1.0`. Pattern fixtures now
check 73 proof-dependency reports, with 27 descriptor and 101 execution reports;
all 201 use only permitted ordinary logical axioms. The positive bridge and
migration composition execute nonempty SQL segments and discharge their frame
premises from branch execution. The tests include raw-trace-sensitive domains,
different hidden prefixes, result-dependent raw/concrete choices, and independent
clock, counter, snapshot and raw-index negatives. The clock case proves weak
preservation on an inhabited domain before refuting full commutation.

The mandatory development build and fixture diagnostics completed before Nix.
Their earlier failures were proof elaboration and fixture syntax issues; no
contract was weakened. Only the Nix result above is acceptance evidence. Logs
remain in `build/agent-logs/migration-composition-*.log`. The focused selector
uses the existing suite and unchanged timeouts. R3/R19 self-review checked raw
reachability, actual/all-branch correspondence and noncircular frame premises.
Independent review `20261025T004439Z-c398676a` read the complete diff and found
zero musts and zero shoulds. This checked boundary remains separate from whole
acceptance-part completion. At that boundary, named commutation identity and
application-composition conveniences, pattern notation/guards/explanations and
source diagnostics were still pending; the fourth unit supplies them. Universal
migration examples with their private guide integration remain required. Rebuild/trigger/INSERT SELECT
examples still depend on their separately owned model work and pending order
decision. Both acceptance parts still require their post-review full/verdict
gates; task end requires Nix and scheduled checks. No such completion is claimed.


## Fourth unit: application composition and pattern frontend

Implementation commit `162849adfa03ebb5d6ce5f6b2fe44d21d8ecb5cb` (Jujutsu
change `ytvpyvlvtswvqvromlvvxyyuqwszzlkx`) has source and fixtures unchanged
from frozen checked revision
`68527f2d3cfc44f358a9cf44042ba5f8b25b60fe`. It adds pure-migration/application commutation, named
application-bind commutation and its same-application/unrestricted conveniences.
The sufficient premise observes every returning first-application branch's raw
reached context and includes migration success there. The target proposition
still uses the original-context success domain. Annotated associativity and the
existing full bind law retain return values and actual/raw/concrete outcomes.

The pattern frontend exposes all four guide spellings, with optional default
`Holds` guards, through the existing fresh primitives and `Runnable`. `quiet`
produces an explicit view descriptor. The minimal `#explain` command elaborates
supported fresh pattern heads before explaining their original-success domain,
vacuity, compared segments, errors and weak/full scope. Unsupported claims receive
an actionable diagnostic. No editor hook, sampler or execution definition changes.

Frozen source passed the installed Nix check at
`/nix/store/wc3x8mr5lynvf1k6620wjcnzjy3b4bzk-sqlite-verifier-test-migration-notation-1`:
10 tests passed, 85 deselected, in 33.72 seconds. The installed surface is
`/nix/store/hm7nvqg5zaaqv2ijxbjyd48h64mifmc5-belay-0.1.0`. The selected tests
check 87 pattern-law, 10 notation, 27 descriptor and 101 execution proof-dependency
reports: all 225 use only permitted ordinary logical axioms. The disposable Nix
selector preserves existing suite timeouts. Log: `build/agent-logs/migration-notation-focused.log`.

The fixtures cover all eight syntax forms, parameterized query admission,
source locations and quiet-action rejection. An explicit original-success
witness makes the nonempty application-composition case nonvacuous and both
orders return its continuation value 8. Raw and concrete LIMIT choices retain
result-dependent tails. A counter guard distinguishes default unknown-counter
observation from a complete zero-counter environment. Actual explanations keep
the written terms and guard, distinguish weak/full context, and retain errors,
stops and vacuity. Failed query admission produces no explanation body.

Mandatory development builds and fixture diagnostics completed before Nix.
Earlier attempts failed on proof-goal ordering, dependent annotation rewriting,
a missing command import, and fixture proof elaboration/reduction bounds; those
were corrected without changing the formulas. Read-only preflight also found
Lean error recovery could leave a failed admission proof in the explanation;
the command now disables that recovery through elaboration and synthesis.
Only the Nix result above is acceptance evidence. Earlier diagnostic logs remain
in `build/agent-logs/migration-notation-*`.

R3/R19 self-review checked proof sketches, raw reached-domain premises, unchanged
original-success domains, retained application values and actual/all-branch
coverage. The frontend reuses the exact fresh predicates and default Holds;
its small explanation function classifies only supported elaborated heads.
Independent review `20261025T011343Z-162849ad` read the diff and tests and
found zero musts and zero shoulds. No model, text-parser, sampler, editor hook
or existing execution definition changed. Universal examples and private-guide
corrections remain unfinished. At this review boundary, post-review full/verdict
and task-end Nix/scheduled checks were still required. The next record completes
the first acceptance part.

## First acceptance part: complete

2026-10-25. Frozen reviewed source
`317cdb1a08623b870823c2a8e55b3207fed67f59` passed the sequential post-review
`just test-full` and `just verdict` checks. The process ended with exit code 0.
The full report is
`/nix/store/307mdy1vcr8yml40rhz473h1b8hbdbbg-sqlite-verifier-test-reports`:
946 tests passed, with no failures, errors or skips. The ten report groups are
corpora 54, documentation 12, frozen 153, harness 234, model 251, packages 3,
parser library 4, sample 23, surface 95 and upstream 117. The full command's
source prerequisite also passed 472 tests and 49 subtests, with 71 tests
deselected by its existing selector.

The verdict is
`/nix/store/fdyxvw89hvk8i7sa232c6is81sczb24d-sqlite-verifier-verdict`:
4,869 AGREE and 2,503 MODEL_UNSUPPORTED across 7,372 cases in 53 groups. There
are no disagreement or unexpected-result categories. This proof/surface part
changes no model execution, frozen corpus, claim or judge lock.

Logs are `build/agent-logs/migration-part1-full.log` and
`build/agent-logs/migration-part1-verdict.log`. The run used one sequential
heavy-process slot, `max-jobs = 1`, `cores = 2`, the existing individual test
timeouts, an 8,400-second aggregate full-check limit and a 5,400-second suite
build limit. Resource checks passed before the full check and verdict.
No source changed while this acceptance ran.

This completes the public views, comparisons, pattern meanings and laws part.
The complete task remains OPEN: universal migration examples, their diagnostics,
private-guide integration and the second acceptance part remain unfinished.
Task-end Nix/scheduled checks have not been claimed or run for this task.

## Part 2: independent normalization examples

2026-10-25. The `s6-migration-examples` workspace starts at reviewed
`317cdb1a08623b870823c2a8e55b3207fed67f59`; the original pattern workspace
retains the completed part-1 acceptance above. The examples now descend from
that evidence-only head, `467cdde5`. Their four shell/resource files
are byte-identical to the approved parent, and the standing-authorized
`direnv allow` completed. No task scope changed.

The counter example is implemented in
`tests/surface/MigrationExpansionCounter.lean`, with its installed/native check
in `tests/surface_migration_examples_test.py`. It uses the complete two-trigger
expansion and public `Sql.runFrom`, states original migration success, compares
the final database and application observations, and refutes full commutation
from totals 3 and 4. The native check reuses validated original SQL annotations.
The focused Nix check passed at
`/nix/store/i2w0ml50phaipdzksffjd79sy4csszh2-sqlite-verifier-test-expansion-counter-1`:
one test passed, 95 deselected, in 4.93 seconds. The existing surface suite's
disposable selector chooses only `expansion_counter`, preserving the installed
artifacts, pinned SQLite tools and existing timeouts. Seven theorem dependency
reports use only ordinary permitted logical axioms. The native replay runs both
orders of the complete four-statement expansion and compares their exact rows,
changes, total_changes and last_insert_rowid with the public model executions.

The mandatory development build completed before this Nix check. Its first
focused attempt failed on a mixed integer/string expected-row literal, which
Lean inferred as strings. Explicit `Value` constructors corrected the fixture;
no model or package definition changed. The failed result is retained in
`build/agent-logs/expansion-counter-focused.log`; the accepted retry is in
`build/agent-logs/expansion-counter-focused-retry.log`. Only the Nix retry above
is acceptance evidence. R3/R19 self-review checked the concrete domain witness,
public support checks, full-context refutation, original-SQL replay validation
and theorem proof sketches. Implementation is immutable
`5600ba9e4620a2fc9e81e5aaac2d8b2a910f6a25`. Independent review
`20261025T014239Z-5600ba9e` found zero musts and zero shoulds. This completes
the separate counter-refutation unit; the universal normalization proofs and
the remainder of the second acceptance part are still unfinished.

The universal normalization proofs can proceed independently of table rebuilds.
All required SQL execution features already exist. Their remaining work is
proof closure over arbitrary admitted rows and parameter values under explicit
physical-table, schema and effect conditions. Existing generated columns and
UPDATE triggers must be covered by those conditions or by derived effect laws;
the desired query equality is not a domain premise. The proofs retain complete
fresh-environment quantification and an inhabited migration-success domain.

Root reserved these proof-only surfaces, with their own narrow registrations:
`packages/belay-sqlite-model/Belay/Sqlite/Model/NormalizedFieldRows.lean`,
`packages/belay-sqlite-model/Belay/Sqlite/Model/NormalizedFieldQueries.lean`, and
`packages/belay/Belay/Sqlite/NormalizedFieldExpansion.lean`. The two model leaves
are checked below; the surface leaf remains unwritten. Execution definitions
remain unchanged. Complete rebuild cascade,
safe-rebuild preservation and affinity examples still require the separately
owned INSERT SELECT, rename and final FK contracts; their earlier prerequisite
status does not block normalization or the counter example.

## Normalization row/query foundation: focused checks complete

This source unit starts at clean counter-review head `b967224a`. It adds
the two reserved model leaves `NormalizedFieldRows.lean` and
`NormalizedFieldQueries.lean`, with only their Model barrel and Lake entries.
The row laws derive the exact result of the existing appended-cell assignment
and UPDATE evaluator under wide-row, no-generated-column and rowid-alias facts.
They preserve old cells, rowids and row order. The query laws compare the
existing simple-query result function, including TEXT comparison affinity for
NULL and every nontext parameter Value. They do not change execution.

`tests/surface/NormalizedFieldLaws.lean` consumes the exported laws with an
arbitrary Value in a nonempty table and an arbitrary parameter Value, plus a
five-storage-class result check. The existing migration-example test module
registers its 14 theorem-dependency audits. On 2026-10-25 the focused Nix surface
check passed both this consumer and the retained expansion counterexample:
**2 passed, 95 deselected**, with zero JUnit failures, errors or skips. Output:
`/nix/store/izbhclljyz1lsgwzysxlbs039q44jkqi-sqlite-verifier-test-normalized-field-1`.
The disposable selector is `normalized_field or expansion_counter`; the existing
suite supplies installed libraries, pinned native SQLite and finite timeouts.
All 21 theorem dependency reports use only the named ordinary logical axioms.
The native counter replay still agrees in both execution orders.

The mandatory development build preceded this Nix check. Its two proof-local
elaboration failures were corrected by an explicit Value.null annotation and
staged simplification; no theorem formula changed. The first Nix attempt passed
the counterexample but failed on a record-layout error in the new consumer.
The fixture correction and axiom-policy/module-documentation cleanup changed
no package source. The final Nix retry reused the exact installed runtime
`/nix/store/hklfgmsd20fnys98grs74aphk54ca7j4-sqlite-verifier-test-surface`.
Failure and retry logs remain in `build/agent-logs/normalized-field-focused.log`
and `build/agent-logs/normalized-field-focused-retry.log`. Only the final Nix
report above is acceptance evidence. R3/R19 self-review checked the proof
sketches, arbitrary Value quantification and supplied-row/result boundary.
Source commit `b81de67c757082a297184c2f82a431583ab246e8` received independent
review `20261025T020558Z-b81de67c`: zero musts and two documentation shoulds.
R6 asks the model module description to state its supplied-row boundary without
referring to a migration user. R2 asks the appended-filter law's text to name
the exact row-width premise. Both corrections are included in the checked scan
unit below, with resolution records and compiled documentation. No formula or
behavior issue was found.

This foundation is not the universal whole-expansion theorem. The reserved
surface `NormalizedFieldExpansion.lean` is still unwritten. That theorem must
derive these input rows from the actual successful ADD COLUMN, backfill and
trigger-registration effects, with concrete schema/effect premises, then lift
the results to actual and every permitted branch over complete fresh
environments. No row-map or desired query equality will be a domain premise.
The scan unit below supplies the source-row bridge, which is separate from
the stored row-list order proved here. The whole second acceptance part
and task-end checks remain unfinished.

## Scan transport: focused checks complete

The next unit starts at `ae0b3f80`, retaining the checked foundation and its
review. Root reserved the new proof-only leaf
`packages/belay-sqlite-model/Belay/Sqlite/Model/NormalizedFieldScan.lean`, with
its own Model barrel and Lake entry. Its public `sourceRows_updated_lower`
statement transports the full scan of the actual appended-column UPDATE to
the corresponding original scan with lowercase cells appended. It assumes
wide aliased rows, in-range original primary-key/source positions and plain
columns. It does not assume scan equality or input row order. Private helpers
transport the existing stable sort using unchanged rowid or primary-key
comparisons, including key directions and collations.

The installed consumer now also supplies three unsorted stored rows whose
rowid order differs from descending NOCASE primary-key order. It applies the
new law under both scan policies and separately checks the two distinct
original orders. The normalization test expects 17 theorem dependency reports;
the retained counterexample still expects seven. The two earlier documentation
shoulds are corrected in the same source batch.

On 2026-10-25 the focused Nix check passed **2 tests, 95 deselected**, with zero
JUnit failures, errors or skips. Output:
`/nix/store/x8ixfbp21dnrrjqz569jgmm33vb087vl-sqlite-verifier-test-normalized-field-scan-1`.
The disposable selector is `normalized_field or expansion_counter`. All 24
theorem dependency reports contain only the named ordinary logical axioms, and
the pinned native counter replay still agrees in both orders. The retained log
is `build/agent-logs/normalized-field-scan-focused.log`.

The mandatory development build preceded this Nix check. Its first attempt
left one definitional-equality proof goal after key-cell rewriting; adding
reflexivity closed it without a formula or runtime change. The failure and
successful retry are retained in `build/agent-logs/normalized-field-scan-dev-build.log`
and `build/agent-logs/normalized-field-scan-dev-build-retry.log`. Only the Nix
report above is acceptance evidence. R3/R19 self-review checked the proof
sketches, unchanged-key comparison argument, unsorted row fixtures and the
limited source-row boundary. Source commit
`90635a75844b8fc9ced6db06ccb1238a36e5f1fb` received independent review
`20261025T022246Z-90635a75`: zero musts and zero shoulds. The reviewer read every
changed file; it did not run tests. This completes the separate scan unit.

At this scan boundary, statement effects, successful original migration, exact
public query output and all raw/concrete branch correspondence were unfinished.
The successful-UPDATE effect gap is closed by the next unit below. Any exclusion of preexisting
UPDATE triggers must be structural or checked against the extended catalog:
an old UPDATE OF name can become a column when ADD COLUMN introduces it.

## Exact UPDATE effects: focused checks complete

The next proof-only unit starts at clean scan-review head `1d70b949`. Root
reserved `Model/NormalizedFieldEffects.lean` and its narrow Model/Lake entries.
The source adds a successful plain-UPDATE inversion to exact `setRows`, its
table-lookup corollary, and the resulting lowercase table/scan laws. Existing
row and scan theorems derive the result; no desired row relation is a premise.
The formulas explicitly require the successful effect and a resolved UPDATE
without a foreign-key or trigger plan. They do not claim that resolution chose
that form or that the statement passes its support check.

The existing installed consumer now checks a real nonempty successful UPDATE
effect and a theorem for every source Value conditional on that effect's
success. The ADD COLUMN operation supplies the starting extended table. Its
23 dependency reports plus the retained counterexample's seven all use only
the named ordinary logical axioms.

On 2026-10-25 the focused Nix check passed **2 tests, 95 deselected**, with zero
JUnit failures, errors or skips. Output:
`/nix/store/9ssgny55hzqh9lvsc1r40zlga0fba65h-sqlite-verifier-test-normalized-field-effects-1`.
The disposable selector is `normalized_field or expansion_counter`. The pinned
native counter replay still agrees in both orders. The retained log is
`build/agent-logs/normalized-field-effects-focused.log`. The mandatory
development build preceded this Nix check; neither check required a source
correction. Only the Nix result is acceptance evidence. R3/R19 self-review
checked the proof sketches, successful-effect boundary, storage-slot premise,
arbitrary Value consumer and actual nonempty success witness. Source commit
`090d363bdf7057689ac4f678a2b40513f67d230b` received independent review
`20261025T024024Z-090d363b`: zero musts and zero shoulds. The reviewer read every
changed file and did not run tests. This completes the exact-effect unit.

The later public-run proof must derive these successful-effect premises from
original migration success and must establish the plain resolved form against
the extended catalog. Whole-script success, query output and all-branch closure
remain unfinished. No execution definition changes in this unit.

The next milestone is the complete four-statement expansion's state theorem
and its public preservation/translation consumers. Add only resolution and
run bridges needed by those theorems. They must retain arbitrary surrounding
catalogs, admitted rows within the explicit schema/effect conditions, arbitrary
parameter Values, original migration success and every complete environment
and raw/concrete branch. The already checked counterexample remains separate
from the positive weak query comparisons.

## Complete expansion state/query proof: focused checks complete

The whole-expansion unit starts at clean effect-review head `cfbb5084`.
Its first uncompiled batch adds `SuccessfulScriptEffects`,
`NormalizedFieldResolution`, `NormalizedFieldUpdateResolution` and
`NormalizedFieldDdlEffects`, with only their model barrel and Lake entries.
These recover the actual successful effect and context, the plain TEXT ADD,
the lower assignment, and the DDL effects around the backfill. The update
trigger condition is exactly an empty `triggersFiring` list for UPDATE of the
old width in the explicitly extended catalog. It does not ban unrelated
triggers or assume a row relation. No execution or resolver definition changes.

The first development compile is diagnostic within this whole-expansion unit.
The composed four-statement state theorem, all-branch/public query consumers
and installed acceptance are not complete. No helper-only acceptance is claimed.

The first diagnostic build on `218d663d` failed in proof elaboration for the
successful-step and resolution bridges. Its log remains at
`build/agent-logs/normalized-expansion-bridges-dev-build.log`. The correction
keeps the formulas and runtime definitions unchanged, fixes Boolean/equality
rewrites and record layout, and clarifies that the ordinary-step law excludes
connection-setting statements as well as transaction control. Dependent
bridges have not compiled yet; no acceptance is claimed.

The bridges compiled after the corrections above. The unit now adds, in the model package,
`SimpleTableRowsOutput`, `NormalizedFieldSelectResolution`, `NormalizedFieldLookups`,
`NormalizedFieldExpandedTable`, `NormalizedFieldLookupOutputs` and `NormalizedFieldExpansion`
(the four-statement state theorem `expansion_state`). In the surface package it adds
`SendStatementsBranches`, `SingleStatementObservations`, `MigrationPatternAfter` and
`NormalizedFieldExpansion`, which holds the public `queryTranslates` and `queryPreserves`
theorems. No execution or resolver definition changed, so the prediction baseline needs no
re-run. Each file has fewer than 200 lines.

The public theorems quantify over every valid database that has a `Site`, every complete
environment and every bound value. A `Site` states that the target table is physical, found by
name at a catalog position, has an id and a source column, has no column of the new name, has
primary-key positions inside its columns and plain (not generated) columns, and that the
catalog with the new field added selects no trigger for an UPDATE of that field. Other tables,
indexes, triggers and rows are unrestricted. Wide and aliased rows come from the database
validity proof. The original migration success, which is the domain of the law, removes the ADD,
UPDATE and trigger-name failures. The foreign-key and recursive-trigger settings are those of
the fresh initial context. The law covers the actual run and every raw and concrete branch,
through the one connection and output count that all migration branches reach.

`tests/surface/NormalizedFieldExpansionLaws.lean` shows that the retained customers expansion is
an instance of the general script (`counter_expansion_is_general`), that its database has a
site, and that both lookup laws give an observation equality at its initial context for every
bound value. The migration-example test module registers it with eight theorem-dependency
reports.

On 2026-10-25 the focused Nix surface check passed **3 passed, 95 deselected**. Output:
`/nix/store/f2dc49k5iyzinx3r5lhrsmi814w803zb-sqlite-verifier-test-surface-1`. The disposable
selector is `normalized_field or expansion_counter`, applied to the existing surface suite with
unchanged timeouts; it was reverted after the run. All eight new reports use only the ordinary
logical axioms, and the retained counterexample and its native replay still pass. The log is
`build/agent-logs/expansion-laws-focused.log`. The mandatory development build
(`build/agent-logs/s6-devbuild-1.log`) preceded it. Only the Nix report is acceptance
evidence. R3/R19 self-review checked the plain-words statements of `Site` and both public
theorems, the proof sketches, and that the trigger premise is the exact structural
`triggersFiring` condition and is not strengthened.
