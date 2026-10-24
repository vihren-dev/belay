# S6 foundations: prototype findings

This record is for designers and reviewers. The prototype is in
`tests/surface/S6*.lean`; it defines no production API. Its Nix acceptance is
recorded in `plans/20261024-surface-s6-foundations.status.md`.

## Predicate transformers and execution

`S6Wp` gives `Std.Do.WPMonad Sql (.arg Context .pure)`. The context contains the
clock function, next statement index, full connection and output trace. Each
step delegates to `runScriptStep`; the prototype adds proof obligations without
resolving or executing SQL itself. `check_bind` proves composition. `check_top`
identifies its unrestricted total-success postcondition with S4 `SucceedsFrom`.
`check_complete_iff` lifts that equality to every complete environment and every
database satisfying an arbitrary predicate. No input is reset between steps.

`check_actual` is the operational soundness theorem: a checked program returns
a value in `Sql.runFrom`, and its postcondition holds at the exact final
connection, accumulated trace and advanced index. `check_allOk` additionally
uses S4's success law to rule out actual errors. The existing
`Sql.runFrom_database_valid` and `Sql.run_outputs` connect this execution with
public `Run`; the validity check cannot add a new failure.

The induction checks the actual output continuation, including raw `oneOf`, and
all concrete `rows` alternatives. Different alternatives may choose different
later statements. The fixtures refute checking only the canonical result and
refute checking only concrete alternatives. A changing clock, counter read
following a write, and rollback across bind check the full context in practice.

The SQL-write triple is proved twice: `mvcgen` uses the checked `writeOne_spec`,
and the other proof uses `Triple.bind` and `Triple.pure` explicitly. The compiler
warns that `mvcgen` is experimental. The semantic instance and checked lemmas do
not depend on that tactic. All audited proofs allow only `propext`,
`Classical.choice` and `Quot.sound`; no semantic assumption is an axiom.

`WPSound` is not an alternative execution theorem that comes with `WPMonad`.
Lean's `Std/Do/WP/Sound.lean` requires an `Internal.Ensures` witness. In
`Std/Do/Internal/Ensures/Def.lean`, that witness is a subtype-refined *monadic
program* whose bind erases to the original program. For the free `Sql` syntax,
this is a structural refinement obligation, not a statement about `runFrom`'s
reachable outputs. No `MonadAttach Sql` or bridge from its `MayReturn` to SQL
execution exists in this base. This prototype does not assert or refute such an
instance. Its direct `check_actual` proof supplies the needed SQL soundness;
a production `WPSound` instance needs its own applicability proof if desired.

The total-success transformer rejects both SQL errors and unmodeled outcomes.
The candidate `ifOk` permits SQL errors but still checks every later continuation
for modeled execution. Its final property is conditional on the entire trace
being successful. Thus an error followed by `random()` cannot prove even a true
postcondition. For fresh triples the trace starts empty. A production API must
say whether a nested conditional claim refers to the entire trace or only the
new suffix; that convenience is not part of this prototype.

## Equivalence and congruence

`S6Equivalence.Visible` compares return values, outputs and the final raw
database at a fixed initial context. Equal raw databases give identical fresh
query observations in the same environment. Checked examples satisfy this
comparison but continuations distinguish them:

| Omitted state | Equal visible prefixes | Distinguishing continuation |
| --- | --- | --- |
| Last-insert counter | Insert id 10 or 20, then erase that row | `last_insert_rowid()` |
| FK pragma | Set `foreign_keys` on or off; both return done 0 | Read that pragma |
| Transaction snapshot | Begin before or after creating a table, then drop it; all outputs are done 0 | Roll back |

The same full-context requirement applies to recursive-trigger settings.
`Connection.resolveState` uses both settings and the snapshot catalog. Ordinary
rowids are in stored rows; they are already part of raw-database equality.
`last_insert_rowid` is separate connection state. AUTOINCREMENT is rejected by
`Translation/Tables.lean`; a checked negative fixture records that scope limit.
There is no current high-water-mark semantics to certify. A future implementation
must include its sequence state in observations or in the continuation relation.

The clock index also matters: the fixture distinguishes the same time query at
indices 0 and 1. Equal output traces from the same initial index already imply
equal next indices by `Sql.runFrom_bind`; this is not an extra independent
condition in that case. Proofs must retain the same clock and prove equivalence
at every reachable index. `Connection.state.clock` is carried unchanged but
`runScriptStep` reads the explicit clock argument, as `ScriptRun.lean` states.

`CheckedEq` combines equality of actual full runs at every execution context
with equality of both-policy transformers for every postcondition. Checked
`bind_right` and `bind_left` establish both congruence directions, including
result-dependent continuations. The existing `send_append` gives script
composition through that same bind. This is sufficient for the observations
in this prototype, and stronger than the guide's visible relation.

It is not a claim of the smallest relation for all possible future observations:
when a concrete alternative becomes unmodeled, its transformer is false and
forgets that alternative's reason and partial trace. Actual-run equality still
retains the actual failure trace. Full equality of alternative failed traces
would need an explicit branch-outcome relation and soundness theorem. No second
execution engine was added to settle that separate design choice.

## The fixed start database in postconditions

The checked `before.t EXCEPT t` fixture is rejected at its schema-qualified
source. `Translation/Sources.lean` rejects a schema name and
`Translation/QueryExpression.lean` rejects a three-part column name. In this
base, `Resolved.Source.table` holds one catalog position, and query evaluation
reads one database. EXCEPT itself is already modeled; its input lookup is the
gap. A database alias alone cannot fix it.

The least additional semantic work is a read-only two-database query context:
keep the start database fixed, identify each source's origin and table position,
and resolve each qualified name against that origin's catalog. Evaluation must
use its rows, rowids and metadata: names, affinity, collation, generated-column
expressions and pragma-source metadata where those sources are admitted. Aliases,
correlated scopes and CTE shadowing must retain their existing rules. A table
alias named `before` must remain distinct from a schema qualification.

The resolved source identity must reach the existing join, expression and
compound evaluators; concatenating two untagged catalogs loses origin and can
change name lookup or EXCEPT collation. A conservative extension theorem should
show that a query without the new qualifier agrees with current evaluation.
A proof-only entry point can expose this context without ATTACH or writable
attached databases. It still needs this small model-level query-context extension;
a second SQL evaluator in the surface would duplicate semantics.

## Read/write premises

Existing pieces are useful but do not give a program footprint:

- `DatabaseWriteLaws.Database.setRows_comm` proves commutation of two *storage*
  updates at distinct positions. It does not establish SQL statement independence.
- `Conforms.setRows`, schema preservation laws and `SqlState.Holds` support
  invariants and frames, provided their premises are discharged.
- `Statement.counterReads`, `clockExpressions` and quiet-statement laws describe
  counter/clock reads. They are not complete table/catalog read sets.
- FK resolution depends on parent tables, declared keys, unique indexes and
  collations. FK actions can read and write child tables; schema changes can
  invalidate parent-key compatibility even without changing rows.
- `TriggerRun` executes WHEN predicates, subqueries, nested writes and raises.
  A statement's target table does not bound those effects. Pragma settings,
  recursion limits, counters and transaction rollback also affect results.

The checked disjoint-table example leaves equal rows and output traces in both
orders, yet its last-insert counter differs. The result-dependent example has
an unchanged actual final database, but a different LIMIT alternative writes
another table. `all_continuations_frame` records the exact required premise:
the first computation must establish the continuation's frame for every actual
and concrete alternative result and its reached context.

Start production proofs with direct semantic frame/commutation lemmas for
restricted statement families. Require stable resolution, disjoint reads and
writes including catalog dependencies, controlled FK/trigger closure, and the
relevant clock/counter/transaction conditions. Full trace equivalence also needs
matching output order; commuting only final rows is a separate weaker claim.
Add a computed footprint only when a specific automation rule needs it and has
a soundness theorem. This experiment does not justify a general effect framework.

## Owner decisions before the full S6 specification

1. **Meaning of equivalence.** Keep visible database equivalence and restrict its
   composition rules, or add a separate context-sensitive relation. Recommend
   separate names: keep the useful visible observation, and require the stronger
   relation for bind/append. `CheckedEq` is an audited starting contract; decide
   whether alternative failed traces are also observable before finalizing it.
2. **Nested conditional triples.** The task already requires modeled execution
   on every branch. Choose whole-run or suffix error scope for nested claims.
   Recommend fresh-run whole traces first and an explicit suffix helper only
   when needed; neither choice permits a model restriction as success.
3. **The start-database qualifier.** Implement general attached databases, or a
   read-only two-database proof context using the model's query evaluator.
   Recommend the bounded proof context with exact origin-aware resolution.
4. **Commutation automation.** Start with direct checked lemmas and explicit
   all-continuation premises, or build a general effect analysis first.
   Recommend the direct lemmas; table-only footprints are already refuted.

Using `mvcgen` is optional once checked specifications and pure/bind rules are
available. No owner decision is needed to retain the explicit-lemma route.
