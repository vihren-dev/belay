# S6: fresh-run triples and initial/current assertions

Created 2026-10-24. Status: OPEN. Implementation follows the reviewed execution
and initial/current query prerequisites. Status: [progress](20261024-s6-assertions.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S6 and the owner decisions
of 2026-10-24; [execution contracts](20261024-s6-execution-contracts.task.md);
[initial/current queries](20261024-s6-before-context.task.md).

## Purpose and boundary

Users can state facts about a fresh SQL program, its returned value, and its
fixed starting and final databases. Ordinary Std.Do triples retain arbitrary
execution contexts for composition. The explicit fresh-run helper states the
entry assumptions that the guide previously omitted. Existing default query
observations keep their meaning; assertions about the real execution context
have separate names.

This task supplies the public assertions, fresh-run helper, proof rules and
universal triple examples. Migration observation views and named equivalence
patterns have another task. Search tactics consume these contracts later;
none of these primitives depends on a particular automation tactic.

## Required outcomes

- **The fresh-run primitive states its entry exactly.** Quantify over every
  bundled valid initial database and every complete Env. Start at statement
  index zero with an empty trace and the ordinary initial connection constructed
  from that database/environment, including the existing profile and counter
  defaults. Accept an arbitrary database precondition and postcondition on the
  captured initial database, returned value and full final context. Use the
  modeled-execution transformer, so a conditional property can permit modeled
  SQL errors but cannot permit unmodeled termination on any branch.
- **Fresh and ordinary triples have a proved bridge.** Prove equivalence to
  the family of ordinary Std.Do triples with exact initial-context equality and
  the stated precondition. Capture the initial database once at the outer entry;
  bind, nested specifications and observations never replace it with an
  intermediate database. Retain ordinary triples and arbitrary context predicates
  as public primitives. Their meaning is not changed by convenient fresh syntax.
- **Current-database assertions preserve existing observations.** The default
  query assertion embeds existing Holds on the reached bundled database, with
  its default environment observation. Prove this correspondence. Preserve the
  existing one-read-only-statement check, parameter bindings, all-permitted-row
  meaning and failure/restriction behavior. Empty, failed or unmodeled queries
  do not establish Holds. A default query assertion does not imply a fresh entry
  or assert facts about the actual clock, counters or connection settings.
- **Context-aware assertions are explicit.** Supply a separately named pure
  assertion that evaluates a query at a supplied execution context. It reads the
  actual clock/index/counters/settings and supports the fixed initial database
  through the initial/current query primitive. The assertion is a logical
  observation: it does not execute an extra program step, advance its index or
  append to its trace. State its output/alternative and error semantics exactly.
  Prove sufficient bridges to default Holds when the query's dependencies make
  the two observations equal; do not assume that all read-only queries qualify.
- **Two-state assertions use the shared query implementation.** A default
  two-state assertion reads before-qualified sources from the captured start
  and ordinary sources from the reached database, using the documented default
  observation inputs. Its context-aware counterpart uses the real context.
  Both consume the same checked parser/resolver/evaluator boundary from the
  prerequisite task. Expose explicit-initial-database constructors as well as
  fresh-run convenience syntax. Preserve SQL source positions and arbitrary
  supported read-only queries; no string replacement implements before.
- **Conditional and total postconditions are usable.** Expose ifOk and andOk
  over the execution task's conditional and total success policies. A fresh
  conditional postcondition requires its
  property when the whole trace has no modeled SQL error; a total one also
  requires that error-free trace. Ordinary triples document how an earlier
  prefix error affects these policies. Both policies require every continuation
  to stay modeled. The returned value remains available to the postcondition.
- **Success has the exact advertised fresh-run equivalence.** Prove that S4
  Succeeds for a script/database predicate is equivalent to the fresh-run triple
  for send with andOk of True. Preserve complete-environment quantification and
  the raw plus all concrete oneOf continuations. Expose the theorem without
  notation. Correct the guide's claim that the same formula needs only a
  default Holds precondition in an unrestricted ordinary triple.
- **Composition preserves the fixed start.** Supply usable pure, bind,
  consequence and conjunction rules for the fresh helper, plus rules that use
  ordinary-context specifications inside it. The bind rule threads the reached
  full context and every permitted value while keeping the original snapshot.
  Postconditions may combine Lean propositions, query facts and returned values.
  Establish soundness for the actual run and every branch through the production
  execution theorems. A fresh proof must not be reused at an arbitrary later
  context without its required entry assumptions.
- **Universal examples state sufficient schema and effect conditions.** Prove
  the guide's insert/lookup, result-dependent successful insertion, preserved
  count and purge-frame claims over every admitted initial database and argument.
  Supply explicit schema, resolution, affinity and trigger/FK conditions needed
  by each claim. A successful trigger may remove the inserted row; a delete
  trigger may remove an unrelated row. Retain kernel-confirmed counterexamples
  and usable structural sufficient conditions for the corrected claims.
  A fixed concrete schema is a test, not a replacement for these universal
  theorems. General semantic frame/effect premises remain available alongside
  structural conveniences; the desired final property is not its own premise.
- **Two-state and invariant examples cover their real behavior.** The purge
  claim compares the unchanged rows with before using the guide's NULL-aware
  IS NOT 1 condition; test nullable parameters and nonnumeric text separately
  from the typed integer-time convenience. Prove an invariant example using
  the appropriate partial unique index and show the ordinary nullable UNIQUE
  counterexample. Error and rollback paths use their actual execution semantics.
- **The surface explains these contracts.** Fresh syntax and assertion notation
  elaborate to the public primitives. Extend the existing explanation path to
  print entry assumptions, fixed-start scope, observation context and error
  policy. Diagnostics identify missing context or an invalid query at its source.
  Update every corresponding private guide occurrence, including the complete
  example, with the accepted meanings and checked proofs. Keep private prose
  and its validation records outside the public repository.

## Tests and acceptance

Kernel fixtures check the helper/ordinary-triple equivalence, Succeeds bridge,
pure/bind rules and fixed-start preservation through two writes and a nested
specification. Include prior SQL errors in ordinary contexts, error then write,
error then unmodeled, all oneOf continuations, returned-output inspection,
changing clock/index, connection counters, pragma settings and rollback.
Default and context-aware query assertions must disagree on an appropriate
counter/clock example, with proved bridges for admitted independent queries.

Installed-library fixtures exercise actual notation, parameter elaboration,
before queries, value binders, explanations and negative diagnostics. Compare
one-state assertions with existing Holds and two-state assertions with the
prerequisite's evaluator. No second interpreter or assumed soundness is allowed.
Check the universal guide claims and concrete counterexamples in the kernel;
audit dependencies for sorryAx, ofReduceBool, _native and semantic axioms.
Use pinned native SQL only as the differential oracle for authored examples.

Two acceptance parts: public fresh/assertion contracts and their proof rules;
universal examples, frontend diagnostics and private guide integration. Each
coherent commit gets focused checks, dev-build and independent review. Each
part ends with post-review just test-full and just verdict. Task-end checks are
just test-nix and just test-scheduled-checks under the existing build-boundary
override. Every subprocess test has a finite timeout. Only Nix results are
implementation acceptance evidence. Existing locked claims remain unchanged;
new corpus evidence follows the separate judge-PR workflow.

## Inputs and ownership

Production S6 contracts and the before-query extension do not exist in this
planning tree. Their task links above identify the prerequisites. The reviewed
prototype/design record is in sqlite-verifier-s6-foundations at c838d5cc;
its five S6 fixtures are design evidence, not production imports. Final S4
provides the valid bundled database/run laws and complete-environment success.
Query-source and before-context work own their model files until integration.

Use packages/belay/Belay/Sqlite/Queries.lean and the final production Context/WP
interfaces. Reserve surface exports, test manifests and the private guide before
editing. Keep assertion construction, fresh-entry laws, notation and example
proofs in modules below 200 lines with checked public documentation. This task
does not add writable attachments, alter default profiles or implement an
independent effect framework. Report a concrete contradiction before changing
an accepted contract; continue independent work while it is resolved.
