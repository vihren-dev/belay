# S6: fresh-run triples and initial/current assertions

Created 2026-10-24. Status: OPEN. Refreshed 2026-10-25 for assignment on the
completed execution contracts (PR #250) and migration patterns part 1 (PR #254,
source `e3baff02`). The initial/current query prerequisite is not implemented.
Status: [progress](20261024-s6-assertions.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S6 and the owner decisions
of 2026-10-24; [execution contracts](20261024-s6-execution-contracts.task.md);
the initial/current query task `20261024-s6-before-context.task.md`, which
stays in the planning workspace and is not carried into this branch.

## Purpose and boundary

Users can state facts about a fresh SQL program, its returned value, and its
fixed starting and final databases. Ordinary Std.Do triples retain arbitrary
execution contexts for composition. The explicit fresh-run helper states the
entry assumptions that the guide previously omitted. Existing default query
observations keep their meaning; assertions about the real execution context
have separate names.

This task supplies the public assertions, proof rules for the fresh-run helper,
the `#explain` command for these contracts and universal triple examples. The
execution contracts already supply the helper, the success policies, the
standard triple instance and the S4 bridge (next section). This task reuses
them and defines no second interpreter. Migration observation views and named
equivalence patterns belong to the migration-pattern task. Search tactics
consume these contracts later; none of these primitives depends on one.

The two-state ("before") assertions need the initial/current query context.
That model task waits for the query-source and view work and has no
implementation. Every outcome that reads `before` is marked as depending on it
and stays in the acceptance of this task. Work that needs only one database
does not wait.

## Existing production interfaces (reuse unchanged)

These exist in `packages/belay/Belay/Sqlite` at `e3baff02`.

- `ExecutionContext` and `ExecutionContext.initial db env`: clock, next index,
  raw connection and trace. The initial context takes the counters of the
  supplied `Env`. It does not force them to zero or to unknown.
- `Sql.Branch`, `Sql.check` with its pure, bind, step, conjunction and
  monotonicity laws, and `Sql.Branch.valid`, which keeps the reached database
  and any open-transaction snapshot valid.
- `FreshTriple` with `iff_triples`, `branch`, `actual` and `succeeds_iff`; the
  success policies `Sql.andOk` and `Sql.ifOk` with `andOk_true_iff`,
  `andOk_empty_iff`, `andOk_ifOk` and `andOk_complete_iff`.
- The `WPMonad` instance `sqlWPMonad`, `Sql.triple_branch`, `Sql.triple_actual`,
  the specifications `send_spec`, `query_spec` and `single_spec`, and
  `check_send_empty`, `check_send_append`, `check_query` and `check_single`.
- `Holds`, `Empty`, `Fails`, `Script.outputOn`, `Script.isQuery` and
  `check_query` of `Queries.lean`; `Succeeds` with the `succeeds where`
  notation; `Env.Complete`.
- The `#explain` command of `MigrationExplainCommand.lean`, with
  `migrationExplanation`. It explains the four migration pattern primitives
  and reports every other proposition as unsupported.

New work: fresh composition rules, the default and context-aware single-state
assertions with their bridges, assertion-level `ifOk` and `andOk`, the fresh
notation, extending `#explain`, the universal examples, and the two-state
assertions.

## Required outcomes

- **The fresh-run primitive keeps its stated entry.** `FreshTriple` quantifies
  every bundled valid initial database satisfying the precondition and every
  complete `Env`. It starts at statement index zero with an empty trace and the
  idle connection built from that database and the environment's counters (no
  open transaction, foreign keys off). It accepts a database precondition and a
  postcondition on the captured database, environment, returned value and full
  final context. It uses the modeled-execution transformer, so a conditional
  property can permit modeled SQL errors but cannot permit an unmodeled stop on
  any branch. This task does not change this definition.
- **Fresh and ordinary triples keep their bridge.** `FreshTriple.iff_triples`
  proves equivalence with the family of ordinary Std.Do triples with exact
  initial-context equality and the stated precondition. New syntax and rules
  capture the initial database once at the outer entry. Bind, nested
  specifications and observations never replace it with an intermediate
  database. Ordinary triples and arbitrary context predicates stay public
  primitives with unchanged meaning.
- **Default query assertions preserve existing observations.** The default
  assertion on an execution context equals `Holds` on the database that the
  context's connection sees, observed as `Holds` observes it: an idle
  connection with no clock, unknown counters, foreign keys off and no open
  transaction. The context stores a raw connection, so the correspondence
  theorem takes a validity proof for that database; for the final context of a
  fresh run, `Sql.Branch.valid` supplies it with no new runtime check or context
  field. At the initial context for any environment, the assertion equals
  `Holds` on the starting bundled database. Preserve the one-read-only-statement
  check, parameter bindings, the all-permitted-row meaning and the failure and
  restriction behavior. Empty, failed or unmodeled queries do not establish the
  assertion. It does not imply a fresh entry or assert facts about the actual
  clock, counters or connection settings.
- **Context-aware assertions are explicit.** A separately named pure assertion
  evaluates a single read-only query at a supplied execution context. It uses
  the actual clock at the next statement index, the actual counters, the
  settings and the connection, with the context's database. It discards the
  observed step's resulting connection and does not execute an extra program
  step, advance the index or append to the trace. State exactly its output
  cases: rows (non-empty), `oneOf` (non-empty list of non-empty results), and
  that an empty result, a SQL error, an unmodeled stop and a non-query output
  all fail to establish it. Expose the underlying output of the real-context
  observation as a public pure function so that users can state other
  observations (empty, failure) without a second interpreter. Prove sufficient
  bridges to the default assertion when the query's dependencies make the two
  observations equal: the resolved statement is a query, resolution succeeds
  identically under both connections, the query reads no clock and no counter,
  and the databases are equal. Do not assume that all read-only queries
  qualify; a clock, counter or pragma-setting query must not.
- **Two-state assertions use the shared query implementation (depends on the
  initial/current query context).** A default two-state assertion reads
  before-qualified sources from the captured start and ordinary sources from
  the reached database, using the documented default observation inputs. Its
  context-aware counterpart uses the real context. Both consume the checked
  parser, resolver and evaluator boundary of the prerequisite task. Expose
  explicit-initial-database constructors as well as fresh-run convenience
  syntax. Preserve SQL source positions and arbitrary supported read-only
  queries; no string replacement implements `before`.
- **Conditional and total postconditions are usable.** Assertion-level `ifOk`
  and `andOk` express the execution task's conditional and total policies in
  ordinary triples and in the fresh notation, and are proved equal to
  `Sql.ifOk` and `Sql.andOk` at the corresponding contexts. A variant that
  also receives the returned value is available. A fresh conditional
  postcondition requires its property when the whole trace has no modeled SQL
  error; a total one also requires that error-free trace. Docstrings state how
  an error in the prefix of an ordinary context affects each policy. Both
  policies require every continuation to stay modeled.
- **Success has the exact advertised fresh-run equivalence.**
  `FreshTriple.succeeds_iff` and `Sql.andOk_complete_iff` prove S4 `Succeeds`
  equal to the fresh-run triple for `send` with an error-free final trace; they
  keep complete-environment quantification and the raw plus all concrete `oneOf`
  continuations. This task adds only the form with the new notation and
  `andOk` of `True`, and the proof that `S succeeds where G` equals it. The
  theorems stay usable without notation. Correct the guide's claim that the same
  formula needs only a default `Holds` precondition in an unrestricted ordinary
  triple.
- **Composition preserves the fixed start.** Supply pure, bind, consequence
  and conjunction rules for `FreshTriple`, and rules that use ordinary-context
  specifications inside it. The bind rule threads the reached full context and
  every permitted value while keeping the original database and environment.
  Postconditions may combine Lean propositions, query facts and returned
  values. Soundness for the actual run and every branch follows from the
  production execution theorems, as `FreshTriple.actual` and
  `FreshTriple.branch` already state. A fresh proof must not be reused at an
  arbitrary later context without its entry assumptions. A kernel fixture
  refutes that reuse.
- **The surface explains these contracts.** Fresh notation and assertion
  notation elaborate to the public primitives. The existing `#explain` command
  accepts, in addition to the migration patterns, a fresh-run triple, an
  ordinary Std.Do triple and `Succeeds`. It prints the entry assumptions (all
  admitted databases, all complete environments, index zero, empty trace, or
  arbitrary contexts for an ordinary triple), the scope of the captured start,
  the observation context of each assertion kind, and the error policy it can
  recognize (`ifOk`, `andOk` or a postcondition that states its own). It
  reports an unsupported proposition at its source, without an invented
  meaning. Diagnostics identify an invalid query (not exactly one read-only
  statement) at its source. A diagnostic for `before` without an initial
  database depends on the initial/current query context.
- **Universal examples state sufficient schema and effect conditions.** Prove
  the guide's insert/lookup, result-dependent successful insertion, preserved
  count and purge-frame claims over every admitted initial database and
  argument. Supply explicit schema, resolution, affinity and trigger/FK
  conditions needed by each claim. A successful trigger may remove the inserted
  row; a delete trigger may remove an unrelated row. Retain kernel-confirmed
  counterexamples and usable structural sufficient conditions for the corrected
  claims. A fixed concrete schema is a test, not a replacement for these
  universal theorems. General semantic frame and effect premises remain
  available alongside structural conveniences; the desired final property is
  not its own premise. The purge-frame claim reads `before` and depends on the
  initial/current query context. The other claims need one database.
- **Two-state and invariant examples cover their real behavior.** The purge
  claim compares the unchanged rows with `before` using the guide's NULL-aware
  `IS NOT 1` condition (depends on the initial/current query context); test
  nullable parameters and nonnumeric text separately from the typed
  integer-time convenience. Prove an invariant example using the appropriate
  partial unique index and show the ordinary nullable `UNIQUE` counterexample;
  these use one database. Error and rollback paths use their actual execution
  semantics.
- **The private guide shows the accepted meanings.** Update every corresponding
  occurrence in the private guide, including the complete example, with the
  accepted meanings and checked proofs. Keep private prose and its validation
  records outside the public repository.

## Tests and acceptance

Kernel fixtures check the composition rules of `FreshTriple` and its use with
ordinary triples, the `ifOk` and `andOk` equalities, the `Succeeds` bridge in
the new notation, and fixed-start preservation through two writes and a nested
specification. Include prior SQL errors in ordinary contexts, error then write,
error then unmodeled, all `oneOf` continuations, returned-output inspection,
changing clock and index, connection counters, pragma settings and rollback.
Default and context-aware query assertions must disagree on an appropriate
counter or clock example and on a pragma-setting example, with proved bridges
for admitted independent queries. A default assertion at a context with a
nonzero index or an open transaction must not imply a fresh entry.

Installed-library fixtures exercise the actual notation, parameter
elaboration, value binders, `#explain` output and negative diagnostics. They
compare the one-state default assertion with existing `Holds`. Fixtures for
`before` queries, and for two-state assertions compared with the prerequisite's
evaluator, wait for the initial/current query context. No second interpreter or
assumed soundness is allowed. Check the universal guide claims and concrete
counterexamples in the kernel; audit dependencies for `sorryAx`,
`ofReduceBool`, `_native` and semantic axioms. Use the pinned native SQL only
as the differential oracle for authored examples.

Three acceptance parts:

1. **Part 1, one-database contracts:** composition rules, default and
   context-aware single-state assertions with their bridges, assertion-level
   `ifOk` and `andOk`, fresh notation and `#explain`.
2. **Part 1b, two-state assertions:** every outcome and fixture marked as
   depending on the initial/current query context. It starts when that task is
   integrated.
3. **Part 2:** universal examples, remaining frontend diagnostics and private
   guide integration.

Each coherent commit gets focused checks, dev-build and independent review. Each
part ends with post-review `just test-full` and `just verdict`. Task-end checks
are `just test-nix` and `just test-scheduled-checks` under the existing
build-boundary override. Every subprocess test has a finite timeout. Only Nix
results are implementation acceptance evidence. Existing locked claims remain
unchanged; new corpus evidence follows the separate judge-PR workflow.

## Inputs and ownership

The production execution contracts (modules `Execution*`) and migration
patterns part 1 (modules `Migration*`, `ExecutionView*`) are in this branch.
The before-query extension is not. The reviewed prototype and design record is
in `sqlite-verifier-s6-foundations` at `c838d5cc`; its five S6 fixtures are
design evidence, not production imports. S4 provides the valid bundled database
and run laws and complete-environment success.

Query-source, view and before-context work own their model files until
integration; S7 owns the SQL-file modules and FK work owns the foreign-key
modules. Do not edit those files. Reserve surface exports (`Belay/Sqlite.lean`
and the library list in `packages/belay/lakefile.lean`), test registrations
and the private guide before editing. Extend `MigrationExplainCommand.lean`
narrowly so that other pattern work merges cleanly. Keep assertion
construction, fresh-entry laws, notation and example proofs in modules below
200 lines with checked public documentation. This task does not add writable
attachments, alter default profiles or implement an independent effect
framework. Report a concrete contradiction before changing an accepted
contract; continue independent work while it is resolved.
