# S6: checked effect rules and reproducible proof automation

Created 2026-10-24. Status: OPEN. Implementation follows the production S6
contracts. Status: [progress](20261024-s6-automation.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S6;
[assertions](20261024-s6-assertions.task.md),
[migration patterns](20261024-s6-migration-patterns.task.md), and
[S5 checker](20261024-surface-s5.task.md).

## Purpose and boundary

The guide promises sql_run, sql_commute and sql_auto that produce kernel-checked
proofs and reusable proof scripts. This task supplies those tactics over the
production semantic contracts. It adds the effect/frame lemmas required by
their advertised SQL examples, with explicit schema and context premises.
The same lemmas remain usable without tactics.

A disjoint-table check is insufficient for full commutation: counters,
catalog resolution, triggers, FK actions, transactions and statement clocks
can connect the computations. The checked prototype demonstrated these cases.
Use direct semantic rules for the supported families and a small conservative
analysis only where a tactic needs it. No general program-effect framework or
alternate SQL execution engine is required.

## Required outcomes

- **Statement rules describe actual effects.** Reuse existing row/schema laws
  and add the missing usable specifications for supported insert, update,
  delete and ADD COLUMN statements required by the guide's assertions and
  migration patterns. Rules state resolution, constraints, conflict handling,
  generated-column, trigger/FK and context assumptions. They cover modeled
  errors and partial effects when applicable. No specification replaces SQL
  execution with an idealized storage update or assumes its own postcondition.
- **Frame rules account for indirect effects.** Expose semantic frame premises
  over every reached branch and usable structural sufficient conditions for
  the guide examples. A target table alone is not the write set. Trigger/FK
  closure, catalog dependencies, generated columns, assigned-column triggers,
  counters, settings and transaction snapshots remain relevant. A missing
  closure proof leaves an explicit goal or unsupported result. Keep flexible
  semantic premises available when structural analysis cannot describe a user
  program; no user must satisfy the tactic's simplifying assumptions.
- **Commutation and preservation have separate rules.** Prove the named
  sufficient rules for weak query preservation/translation and full contextual
  commutation using the production pattern definitions. Full rules require
  equal retained values/traces and full non-trace context, with real clock
  advancement. Different successful change counts or counters cannot be hidden
  by a table frame. Query preservation may use the weaker relation explicitly.
  Restricted-domain rules state preservation at every intermediate context.
- **Dependency analysis produces proof obligations.** For the admitted SQL
  families, identify table, column and catalog dependencies with enough precision
  to prove preservation of a query that reads old columns across an expansion
  which adds/backfills a new column. SELECT star, metadata queries and name
  resolution can observe that expansion and must not receive the same frame.
  Bound parameters remain values, not unseen identifiers. Analysis of unresolved
  SQL proposes dependencies under explicit catalog/resolution premises; it does
  not pretend that a schema is known at elaboration. Prove soundness of each
  certificate used to discharge a semantic condition. The analyzer itself is
  untrusted and may return unknown. Unhandled syntax is never an empty effect.
- **Programs require all continuations.** A program rule covers every actual
  raw continuation and all concrete oneOf alternatives at their reached
  contexts. It may take an explicit semantic bound or prove one compositionally
  from statement rules. An observed run or syntactic inspection of a function
  body is not a universal effect proof. Result-dependent continuations remain
  expressible through the primitive even when automatic analysis stops.
- **sql_run uses checked specifications.** Run mvcgen with the production
  Std.Do specifications and reduce a supported ordinary/fresh triple or pattern
  to the required row, schema, context and branch obligations. Support returned
  values, fixed before snapshots, explicit transactions and both error policies.
  State unsupported goal shapes clearly and preserve unresolved obligations.
  Every automation example also has a proof using explicit public rules, so
  users can avoid experimental mvcgen without changing the proposition.
- **sql_commute proves only the claimed relation.** Discharge an admitted
  preservation or commutation goal from the proved dependency/frame rules and
  available assumptions. A counter/clock/trigger conflict must leave the goal
  open or explain the missing condition. A weaker projected theorem cannot
  close ordinary strong equivalence. The positive expansion read-query example
  succeeds with its stated assumptions; the known full-state write/expansion
  counterexample is refused and remains refutable through S5.
- **sql_auto composes the advertised routes.** Try sql_commute, then sql_run
  with sql_simp, then grind with the intended lemma collection. Reuse existing
  S4 sql_simp/query laws and S5's proof-search entry rather than duplicating
  them. Restore tactic state between unsuccessful alternatives. All success
  paths return proof terms checked by Lean's kernel; timeouts and unsupported
  goals cannot produce an admitted theorem. Keep explicit tactics and lemmas
  accessible independently of the combined search.
- **Successful search gives a reusable proof.** Offer the guide's Try this
  script and editor code action. The replacement uses checked named rules and
  stable explicit tactic steps, with required arguments and generated names in
  scope. Re-elaborating it proves the original proposition without rerunning
  sql_auto or candidate search. Do not offer a script that silently changes
  hypotheses, the observation view or the current namespace/options.
- **The existing checker covers S6 claims.** Integrate triples, the equivalence
  variants and named patterns with S5's proved/false/unknown result contract,
  explicit/search refutation, budgets and background checking. A false witness
  identifies its initial database, complete environment when required, inputs,
  branch and failing observation. Initial-domain membership is certified.
  Counterexamples involving a raw Lean continuation are described accurately;
  they are not mislabeled as native statement failures. Reuse the established
  replay/certification path, retaining unknown for unsupported certification.
- **The guide examples have checked scripts.** Check the corrected insertion,
  purge-frame, partial-index invariant, query equivalence, expansion read-query
  and rebuild claims with the advertised routes and explicit premises. Keep
  their counterexamples. Update all private guide tactic/footprint descriptions
  to state the actual supported analysis and remaining obligations. The scope
  of the primitive contracts is unchanged by automation coverage. S8 later
  supplies its own interface-scoped call proofs to the same public mechanisms.

## Tests and acceptance

Nix-selected installed-library fixtures prove a nontrivial statement effect,
frame, conditional/total fresh triple and migration query pattern using the
intended tactic, then prove the same propositions with explicit rules. Include
parameterized universal claims and a noncanonical oneOf continuation that writes
another table. A representative multi-step program keeps its initial snapshot
and open transaction across intermediate specifications.

Negative fixtures cover SELECT star and catalog metadata after ADD COLUMN,
trigger/FK cross-table writes, generated columns, counter reads, clock-sensitive
migrations, rollback snapshots, different change-count outputs, and unmodeled
syntax. Supply a deliberately invalid dependency certificate; its soundness
obligation must fail. A failed tactic attempt must preserve the original goal.
Do not compare a tactic's own output with itself as its correctness oracle.

Through the editor protocol, request/apply/recheck proof and regression code
actions with source ranges, namespaces, local variables and options. Exercise
all S5 result classes, budget exhaustion and cancellation on the new claim
forms. Recheck emitted proof scripts with search disabled. Audit their axiom
dependencies for sorryAx, ofReduceBool, _native and assumed effect soundness.

Two acceptance parts: required effect/frame specifications and conservative
dependency certificates; tactics, checker/code-action integration and corrected
guide examples. Each coherent commit gets focused checks, dev-build and review.
Each part ends with post-review just test-full and just verdict. At task end
run just test-nix and just test-scheduled-checks under the build-boundary
override. Every subprocess test has a finite timeout. Only Nix results are
acceptance evidence. No judge/corpus/lock change is planned; any required new
evidence uses a separate judge PR.

## Inputs and ownership

The linked production contracts and S5 are not implemented in this planning
tree. Integrate their final reviewed boundaries first. The checked prototype
and effect counterexamples are in sqlite-verifier-s6-foundations at c838d5cc,
with completed acceptance at eb0a16a9. Existing model pieces include
DatabaseWriteLaws, WriteLaws, TriggerRun, Statement.counterReads and clock laws;
these are useful inputs, not a proved whole-program footprint. Final FK work
supplies the split schema/row-reference conditions and selected action mapping.

Reserve the surface barrel, tactic registries, S5 checker entry, test manifests
and private guide before editing. Keep certificate semantics, analysis, tactic
execution and proof-script rendering separate, below 200 lines per module.
Use checked public docs and plain-words theorem contracts. Do not change SQL
meaning or add a general effect framework to simplify automation. Report a
demonstrated semantic contradiction before changing an accepted contract.
