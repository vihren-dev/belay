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
and pattern frontend have the focused evidence below. The fourth unit awaits
independent review. Universal examples, private-guide corrections and the
acceptance-part checks remain required.

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

The implementation is in Jujutsu change `ytvpyvlvtswvqvromlvvxyyuqwszzlkx`,
with source and fixtures unchanged from frozen checked revision
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
Independent review is pending. No model, text-parser, sampler, editor hook or
existing execution definition changed. Universal examples and private-guide
corrections remain unfinished. Neither acceptance part is complete; post-review
full/verdict and task-end Nix/scheduled checks remain required.
