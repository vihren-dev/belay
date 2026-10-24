# S6: execution branches, predicate transformers and equivalence

Created 2026-10-24. Status: OPEN. Implementation follows task review and the
final S4 execution interfaces.
Status: [progress](20261024-s6-execution-contracts.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S6 clarification accepted
2026-10-24; [foundations prototype](20261024-surface-s6-foundations.task.md).

## Purpose and boundary

This task supplies the production execution and proof primitives for S6.
The checked prototype established pure/bind rules and actual-run soundness, but
its transformer comparison forgets failed alternative traces. The accepted
strong equivalence must retain them. These primitives also let later migration
patterns use a named weaker observation without changing ordinary execution.

This task does not complete S6. Public query assertions and their fixed initial
database, migration observation views, named patterns, automation and corrected
guide proofs have separate acceptance work. The pending quiet-view decision
does not change the complete execution contract specified here. No second SQL
resolver or evaluator, new model feature or general effect framework is needed.

## Required outcomes

- **Execution has an exact branch relation.** For a program, supplied clock,
  starting statement index and full connection, a complete branch outcome keeps
  its optional return value, full output trace and final connection. Each step
  uses the existing `runScriptStep`. A continued raw output always reaches its
  actual continuation. A `oneOf` output additionally permits each listed
  concrete rows result at the same next connection. The selected output reaches
  both the continuation and that branch's trace. Repeated alternatives do not
  add observations beyond set membership; the actual raw wrapper is retained.
- **Errors keep their actual meaning.** A modeled SQL error continues through
  the program, including later writes and errors. An unmodeled step ends it,
  retains its reason and prefix trace, and has no return value. Bind cannot run
  a continuation after such a stopped prefix. Empty alternative lists still
  have the raw continuation. No branch can disappear because it fails a proof
  condition. The executed-step count, including a stopping step, determines the
  next index where a continuation is permitted.
- **Branch composition is proved.** Establish actual-run membership, pure,
  execution-step and bind characterizations. Bind composes every returning
  prefix with every continuation outcome from its exact reached context; a
  stopped prefix remains stopped. Carry the same clock throughout. Prove
  database validity for every reached branch from a valid connection state,
  including a valid open-transaction snapshot. This extends S4's actual-run
  validity theorem without deciding validity again or assuming a branch law.
- **The transformer agrees with branches.** A predicate transformer checks a
  postcondition on the value and complete reached context of every branch and
  rejects any unmodeled outcome. Modeled SQL errors may continue; a separate
  success condition requires an error-free trace. Prove the transformer's
  equivalence to this branch contract, its conjunction law and its pure/bind
  laws. A recursive implementation may reuse the prototype's proof structure,
  but transformer equality alone must not replace the branch outcome relation.
- **Standard triples have operational soundness.** Supply the production
  `Std.Do.WPMonad` instance for `Sql` and checked pure/bind/step specifications.
  Prove that its triples imply their postconditions for the actual execution
  and every permitted branch under their stated context preconditions. The
  full context retains the trace, clock, next index, counters, settings and
  snapshots; bind does not create a fresh connection. Keep the low-level context
  and arbitrary postconditions public. A `WPMonad` class instance is not itself
  a soundness theorem. Do not claim `WPSound` without proving its additional
  structural applicability obligations for this free program type.
- **Conditional and total success are distinct.** Provide trace predicates or
  postcondition combinators for both policies. For a fresh run, conditional
  success checks the final property if no modeled SQL error occurred anywhere
  in that run; total success requires both the final property and no such error.
  Both require modeled execution of every continuation. An error followed by
  an unmodeled step cannot discharge even a true conditional postcondition.
  State explicitly how an existing prefix trace affects the primitive; the
  fresh-run helper starts with an empty trace. Do not install the prototype's
  error-rejecting transformer as the only route to conditional triples.
- **S4 success has an exact bridge.** At an empty prefix, the total-success
  transformer with a true final property is equivalent to `Sql.SucceedsFrom`
  at the same clock/index/connection. Lift this to S4 `Succeeds` over every
  bundled database satisfying the supplied predicate and every complete `Env`.
  Preserve both raw and concrete continuation obligations. The bridge must
  not identify a default-environment observation with universal success.
- **Strong equivalence retains complete observations.** Define the primitive
  intended for ordinary `≈` as equality of actual full runs and equality of
  the sets of complete branch outcomes at every shared clock, index and full
  connection. Compare errors and unmodeled reasons/partial traces too. Include
  return values and all connection state, even when final tables agree. A
  fixed-context relation and an explicitly restricted-domain primitive remain
  available; the unrestricted relation supplies composition without hidden
  reachability assumptions. This task may expose the ordinary notation after
  its primitive is fixed; it must not assign that notation to a weaker view.
- **Equivalence composes.** Prove reflexivity, symmetry, transitivity, both bind
  congruence directions and script append congruence through `send`. Cover
  result-dependent continuations. Restricted-domain variants name the context
  and precondition-preservation premises they need. Equivalence transports the
  transformer and success claims. Also expose a separately named comparison
  of return values and outputs with final connections omitted; it carries no
  unrestricted bind/append congruence. Observation masking belongs to the
  later migration-pattern task, not to the execution relation.
- **Users can prove the same fact without a tactic dependency.** A small SQL
  write example compiles both with `mvcgen` using checked specification lemmas
  and with explicit pure/bind/step rules. Use the existing `send`, `query`,
  `single` and transaction helpers in compositional specifications, preserving
  their actual error handling and context effects. The explicit route remains
  usable if experimental automation changes. A convenience rule must leave the
  arbitrary `Sql.exec` continuation and postcondition primitives accessible.

## Tests and acceptance

Nix-selected installed-surface fixtures cover pure, empty and multi-statement
scripts, data-dependent bind, actual raw oneOf inspection, every concrete LIMIT
tie branch, repeated/empty alternatives, and an alternative that becomes
unmodeled with a distinct reason after a partial trace. Include SQL error then
write, error then unmodeled, changing clocks, counter reads after writes,
pragma settings and rollback across bind. Public Run observations must agree
with the actual branch without restoring the removed validity decision.

Kernel-checked positive and negative examples distinguish actual-run equality
from all-branch equality, successful-transformer equality from failed-trace
equality, and visible equality from full-context equality. Retain the prototype's
counter, pragma and transaction-snapshot continuation counterexamples. Test
both congruence directions and a restricted-domain rule whose preservation
premise is essential. A false universal law is refuted, not merely left unproved.

Check conditional/total policies separately, their exact S4 bridge, and the same
nontrivial triple by mvcgen and explicit lemmas. Audit theorem dependencies for
`sorryAx`, `ofReduceBool`, `_native` and assumed semantic soundness. Use checked
public docstrings, plain-words proposition contracts and proof sketches.

Two acceptance parts: exact branches and the transformer/operational bridges;
equivalence/composition and compositional helper specifications. These are
observable boundaries, not prescribed implementation steps. Each coherent
commit gets focused tests, dev-build and independent review. After each part's
final review run `just test-full` and `just verdict`; at task end run
`just test-nix` and `just test-scheduled-checks`, following the owner's override
in [the build-boundary status](20261024-text-build-boundaries.status.md).
All subprocess tests have finite timeouts. Only Nix results are acceptance
evidence. Existing predictions and the judge lock must remain unchanged.

## Existing interfaces and ownership

Consume final S4 `Program`, `ProgramRun`, `ProgramBindLaws`, `ProgramSuccess`,
`Env.Complete`, run/output/validity laws and the removal of `Run.checked`.
The prototype's five `tests/surface/S6*.lean` modules and its design record are
checked design inputs, not production imports. Keep context, branch laws,
transformer laws and equivalence laws in modules with separate contracts,
below 200 lines each. Export them through the surface package only; model and
conformance imports keep their current dependency boundaries.

Reserve shared Lake/barrel and test-manifest entries before implementation.
The initial/current query task owns its model changes separately. No new query
semantics or private guide prose belongs in these execution modules. Stop the
affected branch for a demonstrated specification contradiction; continue the
independent work. This task's completion must not be reported as completion
of public assertions, migration patterns, S6 automation or S6 as a whole.
