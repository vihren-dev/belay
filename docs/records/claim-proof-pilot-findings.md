# Claim proof pilot: findings

Audience: the team and the owner. Status: the pilot is complete; the
owner decision is open. Contract:
[task](../../plans/20261124-claim-proof-pilot.task.md).

The pilot proves two claims about one DELETE in a base form and in four
other forms. This record compares the forms and gives a recommendation.
All measurements are local. They are data for the decision. They are not
evidence of a check.

## Result

- Recommended: claims stay SQL queries, the library has one law for each
  operator of a query (form B), and a tactic applies the laws (form C).
  Two parts of the other forms join them: the exact rows that a write
  leaves, as a library fact (from form A), and the analysis that shows
  that a write runs on each database with a given catalog (from form
  D), as a step of `sql_run`.
- Not recommended as the main form: claims as Lean propositions only
  (form A), because the claim is then outside SQL; and a checker for
  each pattern of claim (form D), because a pattern costs 76 package
  lines (the effect check) or 163 (the frame check, with its model
  laws), and a refused claim gets no reason.
- The form of today, one law for one form of query, has no advantage
  that another form does not have. Form B proves its four laws from the
  laws of the parts.

The section [Recommendation](#recommendation) gives the reasons and the
steps.

## The forms

| Form | What it is | Branch | Last Lean change |
| --- | --- | --- | --- |
| Start | `adr-0033-phase-8-inventory` | | `1e8dfd8d` |
| Base | One law for one form of query, with no assumed premise | `claim-proof-pilot` | `29676e82` |
| A | The claim is a Lean proposition about rows | `claim-proof-pilot-logic` | `a1705c06` |
| B | One law for each operator; the proof composes them | `claim-proof-pilot-laws` | `0f070f76` |
| C | A tactic applies the laws of B | `claim-proof-pilot-tactic` | `5bc3c323` |
| D | A check to `Bool` with a theorem of soundness | `claim-proof-pilot-checker` | `8e136beb` |

Forms A, B and D start from the revision `ff882f8d` of the base form,
which has the Lean code of `29676e82`. Form C starts from form B.
Each form is the usual answer of a field of verification practice:

- A: the specification is written in the logic of the prover, as in
  Dafny, Why3 or the abstract specifications of seL4.
- B: a library of laws for each operator of the language, as in
  CompCert or Mathlib.
- C: a tactic that walks the program and leaves verification conditions,
  as the proof mode of Iris, `forward` of VST or `mvcgen` of Lean.
- D: a certified checker, as the validators of CompCert or the
  reflective tactics `ring` and `lia`.

## The two claims

The purge is `DELETE FROM sessions WHERE customer_id = :c AND expires_at
< :now` on the schema `sessions (id INTEGER PRIMARY KEY, customer_id
INTEGER NOT NULL, expires_at INTEGER NOT NULL)`.

- Frame claim: the purge keeps each session that it is not meant to
  delete.
- Effect claim: after the purge, no session is left that its filter
  selects.

Each client statement holds for each pair of values, also NULL and text,
for each valid database with the catalog of the schema, and for each
complete environment. It has no other premise. It requires two things
of the run of the purge from the fresh start. Each branch of the run
stays in the model, also a branch that gives a SQL error. Each branch
with no SQL error ends in a context in which the claim holds. A SQL
error that the model gives waives only the claim.

### Statements with the claim in SQL (base form, B, C, D)

```lean
def purge := sql r"DELETE FROM sessions WHERE customer_id = :c AND expires_at < :now"

def purgeKeeps (c now : Value) : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT * FROM before.sessions WHERE (customer_id = $c AND expires_at < $now) IS NOT 1 EXCEPT SELECT * FROM sessions)"

def purgeClears (c now : Value) : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE customer_id = $c AND expires_at < $now)"

theorem purge_frame_on_sessions (c now : Value) :
    FreshEnsuresFrom (send (purge c now)) (·.HasCatalog sessions)
      (fun start => ifOk (holdsSince start (purgeKeeps c now)))

theorem purge_clears (c now : Value) :
    FreshEnsures (send (purge c now)) (·.HasCatalog sessions) (ifOk (holds (purgeClears c now)))
```

The four forms prove these two statements unchanged. Form C names its
theorems `purge_frame_by_tactic` and `purge_clears_by_tactic`. Form D
names them `purge_frame_by_check` and `purge_clears_by_check`.

### Statements in form A

With the resolved filter of the purge, `purgeFilter`:

```lean
theorem purge_keeps_unselected_rows (c now : Value) :
    FreshEnsuresFrom (send (purge c now)) (·.HasCatalog sessions) fun start =>
      ifOk fun final => ⌜∀ row ∈ (start.rows "sessions").getD [],
        Resolved.truthy (purgeFilter.eval (.bound [c, now]) row) = false → row ∈ (final.rows "sessions").getD []⌝

theorem purge_leaves_no_selected_row (c now : Value) :
    FreshEnsures (send (purge c now)) (·.HasCatalog sessions)
      (ifOk fun final => ⌜∀ row ∈ (final.rows "sessions").getD [],
        Resolved.truthy (purgeFilter.eval (.bound [c, now]) row) = false⌝)
```

With a predicate on the cells:

```lean
abbrev comparesAsInteger (cell value : Value) (order : Ordering) : Prop :=
  (Resolved.numericOperand cell).isNull = false ∧ (Resolved.numericOperand (boundValue value)).isNull = false ∧
    Value.compare (Resolved.numericOperand cell) (Resolved.numericOperand (boundValue value)) = order

abbrev expiredSessionOf (c now : Value) (row : List Value) : Prop :=
  comparesAsInteger (row.getD 1 .null) c .eq ∧ comparesAsInteger (row.getD 2 .null) now .lt

theorem purge_keeps_live_sessions (c now : Value) :
    FreshEnsuresFrom (send (purge c now)) (·.HasCatalog sessions) fun start =>
      ifOk fun final => ⌜∀ row ∈ (start.rows "sessions").getD [],
        ¬ expiredSessionOf c now row → row ∈ (final.rows "sessions").getD []⌝

theorem purge_leaves_no_expired_session (c now : Value) :
    FreshEnsures (send (purge c now)) (·.HasCatalog sessions)
      (ifOk fun final => ⌜∀ row ∈ (final.rows "sessions").getD [], ¬ expiredSessionOf c now row⌝)
```

All four follow from one helper, `purge_reached_rows`: a row is in the
reached table exactly when it is in the table of the start and the
filter is not true for it.

## Client cost

Code lines as `scc` counts them: no blank lines, comments or docstrings.
"Statement / proof" gives the lines up to `:=` and the lines after it.

| Form | Frame claim | Effect claim | Helpers of the claim | Helpers that run the purge |
| --- | --- | --- | --- | --- |
| Start | 6 / 27 and 3 / 7 | not proved | 22 | site with assumed facts |
| Base | 6 / 27, 3 / 7 and 3 / 1 | 4 / 16 and 2 / 21 | 22 | 43 |
| A | 4 / 2 | 4 / 2 | 4 / 21, shared by both claims | 43 |
| B | 6 / 71, 3 / 7 and 3 / 1 | 4 / 30 and 2 / 20 | 31 and 4 | 43 |
| C | 3 / 29 | 2 / 18 | none | 43 |
| D | 3 / 2 | 2 / 2 | none | none |

- "Helpers of the claim" are definitions and lemmas that restate parts
  of the resolved claim (`PurgeFrameQueries.lean`,
  `PurgeEffectClaims.lean`). Form A needs none of them. Its two
  statements with the predicate on the cells cost more: the predicate
  (5 lines), a bridge to the resolved filter (2 / 2), and the two
  theorems (4 / 3 and 3 / 3).
- "Helpers that run the purge" are `PurgeFrameSite` (12),
  `PurgeFrameSite.purge_continues` (3 / 10), `sessions_found` (2 / 2)
  and `sessionsSite` (14). They show that the purge resolves and
  continues on each database with the catalog. Each form but D uses
  them. Form D gets the same fact from its analysis of the DELETE, for
  each schema.
- In each proof of form C, 10 of the proof lines repeat the call of
  `sql_run` with these helpers. The lines after `sql_holds` are 7 for
  the effect claim and 18 for the frame claim.
- Form C proved a third claim, "the purge adds no session"
  (`purge_adds_none`, 3 / 24), with no change of a package.
- Form B alone makes the client proofs longer than the base form: the
  client composes the laws by hand. Form C removes that work.

## Code change

Net change of the maintained Lean code lines from the start revision
(98,829 lines), with `scc` 3.7.0 as
`docs/development/lean-simplification-goal.md` uses it.

| Form | Model package | Surface package | Tests | Total | Against the base form |
| --- | --- | --- | --- | --- | --- |
| Base | +20 | 0 | +120 | +140 | |
| A | +30 | +9 | +260 | +299 | +159 |
| B | −78 | +37 | +337 | +296 | +156 |
| C, with B | −5 | +363 | +501 | +859 | +719 |
| D | +111 | +342 | +101 | +554 | +414 |

- The tests of form B include the retention fixtures with 147 lines.
  They prove the statements of the four deleted laws from the laws that
  remain. The tests of form C include the proofs of form B, which stay
  for the comparison: a branch for a pull request keeps one proof of
  each claim.
- Base: the 20 package lines are the readiness facts of a DELETE with a
  row-wise filter. They serve each such DELETE. At the start, nine model
  modules with 429 lines hold the laws that the frame proof calls. One
  of them, `RowwiseExpr` (61 lines at `29676e82`), is shared:
  `ClaimsExpressionCongruence.lean` uses `Resolved.Expr.Rowwise`. The
  others serve only the query form of the frame claim.
- A: 19 package lines more than the base form, 39 from the start. The
  19 lines are general: `LiteralData.mem_deleted_rows` and
  `ExecutionContext.rows`.
- B: the new laws have 231 lines, and the deleted laws of the one query
  form have 292. No new law names a form of claim.
- C: the tactic has 273 lines, the bridge laws over a catalog 50, and
  new model laws 73. None names the purge. The tactic knows the forms
  that the section "Reach" lists.
- D: the analysis of a plain DELETE and its send theorem (92 lines) and
  31 model lines (`isRowwise` with its soundness, a bound of a table
  position) serve each check of a claim about a plain DELETE. The
  effect check (76 lines) serves one pattern of claim. The frame check
  with its shape (130 lines) and 33 model lines (`isTruthValued`,
  `truthy_isNot_one`, `exceptSubqueries`) serve the other pattern. 69
  lines moved from a test support file to the packages.

## Trust and premises

In each form the kernel checks the proof, and each client theorem
depends on `propext`, `Classical.choice` and `Quot.sound` only. A reader
trusts the model and reads the statement. The forms differ in what the
reader must read.

| Form | What the reader reads | Premises that the client proves |
| --- | --- | --- |
| Base, B, C | The SQL text of the claim | None in the statement. In the proof: that the purge resolves and continues, the subset step, the identity of rows that compare equal |
| A | A Lean proposition with the resolved filter or with a predicate on the cells | None in the statement. In the proof: that the purge resolves and continues |
| D | The SQL text of the claim, and the docstring of the check to know its limits | None. The kernel evaluates the check |

- A claim in SQL has the meaning that SQLite gives the query. The
  conformance corpora compare the model with native SQLite for the
  operations of such a query. The pilot does not run the two claims on
  native SQLite: the instance fixtures evaluate them in the model.
- A claim in Lean has no native reading. The predicate on the cells
  must follow the rules of SQLite: a text `'1'` matches the integer 1
  in a column with INTEGER affinity, and NULL matches nothing. A plain
  `row[1] = c` is wrong. The resolved filter avoids the trap, but a
  reader must know the model to read it.
- The tactic of form C and the checks of form D are not trusted. The
  tactic builds a proof term that the kernel checks. The checks have
  theorems of soundness, and `decide +kernel` evaluates them in the
  kernel.

## Traps that the pilot found

- When `f` gives 0, 1 or NULL, a row with `f IS NOT 1` is a row that
  the DELETE does not select. This range is a sufficient condition.
  Without it there is no guarantee: `DELETE … WHERE 2` deletes each
  row, and `2 IS NOT 1` is true for each row, so the frame claim of the
  guide is false. A filter that is one column can give 2. Form B states
  the law for a value: for a value that is NULL, 0 or 1, `IS NOT 1` is
  true exactly when the value is not true (`Value.truthy_isNot_one`).
  Its law for an expression (`Resolved.Expr.truthy_isNot_one`) has
  narrower premises: the top operator of the expression is a
  comparison, `AND`, `OR`, `NOT`, `IS NULL`, `EXISTS` or `IN`
  (`Resolved.Expr.isLogical`), and the comparison `IS NOT 1` has no
  affinity. It does not cover a literal 1. The frame check of form D
  refuses a filter whose top operator does not establish the range.
- A filter with a subquery can select a row after the DELETE that it
  did not select before. The effect claim is then not a consequence of
  the DELETE.
- A missing table reads as "no rows" in form A, so an effect claim in
  Lean holds for it. The claim in SQL gives an error.
- A helper of `sql_select` accepted a false equation and reported the
  error only at the end of the declaration, because the kernel check
  ran in a background task. Form C fixes it (`evaluationProof?`). The
  fix does not depend on the owner decision.

## Reach

| Form | Claims it can state and prove today | Cost of a claim outside |
| --- | --- | --- |
| Base | A claim whose query form has a law | A law for the new form. The form of the frame claim costs about 290 package lines |
| A | Each proposition about the rows before and after a write whose data fact exists | A data fact for the write kind, and Lean functions for joins, aggregates and collations when the claim needs them |
| B | Each claim whose operators have laws; the client composes them | A law for the operator, which then serves each claim |
| C | `SELECT 1 WHERE [NOT] EXISTS (q)`, where `q` reads one table of the current or the initial database with row-wise expressions, or is an `EXCEPT` of two such reads | A law (form B) and a case of the tactic. The laws stay usable by hand |
| D | A script of one DELETE with a WHERE whose filter is row-wise, on a table of the schema, with no RETURNING, trigger or foreign-key action. Effect check: the claim `SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM t WHERE f)` with the resolved table and filter of the DELETE. Frame check: the claim of the guide's form, a filter whose top operator is a comparison, `AND`, `OR`, `NOT` or `IS NULL`, and a table whose first column is the rowid alias. Both checks ignore the values that the two scripts carry: the guarantee is for the DELETE and the claim with one shared list of values | A check with its theorem of soundness for each new pattern |

Measured: the effect claim. The base form needed 43 client lines and
no package law, because a law for its query form was in a test support
file (72 lines). Form A needed 6 lines after the helper. Form B needed
56 theorem lines and 4 helper lines, with the laws that the frame claim
needs too. Form C needed 20 lines. Form D needed 76 package lines and 4
client lines.

Measured: the third claim of form C, 27 client lines and no package
change.

Estimate, not measured: the frame claim of a plain UPDATE. Each form
needs a readiness fact for the SET expressions (about 20 lines) and a
data fact that an UPDATE does not change a row that its filter does not
select (about 30 lines).

| Form | More package lines | Client lines |
| --- | --- | --- |
| Base | about 40, a law of the query form for `LiteralData.updated` | about 110, as for the purge |
| A | none | about 30, a helper and the statement |
| B | none | about 120, as for the purge |
| C | none | about 30 |
| D | 130 to 200: analysis, send theorem and check | 5 |

## Elaboration time

Local, lower of two runs, at different machine loads. The fixture times
are from the compile of the purge test, as the status file of each
branch records them.

| Fixture | Time |
| --- | --- |
| Base: `PurgeFrameQueries`, `PurgeFrameSite`, `PurgeFrameClaims`, `PurgeFrameSchema` | 1.0 s, 1.0 s, 1.3 s, 1.3 s |
| Base: `SelectOneWhereSupport`, `PurgeEffectClaims` | 1.0 s, 1.2 s |
| Base: `PurgeFrameInstances`, `PurgeEffectInstances` | 3.1 s, 1.7 s |
| A: `PurgeLogicClaims`, `PurgeLogicInstances` | 1.9 s, 2.4 s |
| B: `PurgeFrameQueries`, `PurgeFrameSite`, `PurgeFrameClaims`, `PurgeFrameSchema`, `PurgeEffectClaims` | 1.2 s, 1.0 s, 1.4 s, 1.4 s, 1.3 s |
| B: `PurgeFrameInstances`, `PurgeEffectInstances` | 3.3 s, 1.7 s |
| B: `PurgeLawRetention`, `PurgeLawRetentionOutput` | 0.9 s, 1.1 s |
| C: `PurgeEffectTactic`, `PurgeFrameTactic` (two claims), `PurgeTacticCases` | 1.6 s, 3.6 s, 4.4 s |
| C: one call of `sql_holds`, with the profiler | 0.3 s to 0.8 s |
| D: `PurgeCheckClaims`, at the revision `3a0d4fe8` with six limit examples | 3.7 s |
| D: kernel evaluation of the frame check and of the effect check | 0.21 s, 0.12 s |

New and changed library modules. The times with "Lake" are from
`lake lean` at the last code revision and include about 0.3 s to 0.8 s
of Lake. The other times are from `lake env lean` or from
`just dev-build`.

| Module | Time |
| --- | --- |
| Base, model: `QueryPlainLaws`, `RowwiseExpr`, `JsonReadyLaws` | 2.0 s, 0.5 s, 0.3 s |
| A, model: `RowDeleteLaws` | 0.3 s |
| A, surface: `ContextRows` | 1.9 s (Lake) |
| B, model: `LogicalValueLaws`, `RowwiseExpr`, `ExprEvalLaws`, `RowidOutputIdentity` | 1.3 s, 0.5 s, 0.5 s, 0.4 s |
| B, model: `RowDelete`, `SelectSubqueryRules`, `Subqueries`, `Tooling/Counterexamples/TwoStateQuerySteps` | 0.3 s, 0.4 s, 0.4 s, 1.6 s |
| B, model: `Schema/Dispatch/TwoStateQuerySteps` | 0.5 s (Lake) |
| B, surface: `ResolvedOutputBridge` | 1.0 s |
| C, model: `RowwiseCheck`, `RowwiseExpr`, `ExprFormChecks`, `DatabaseLookup` | 0.9 s, 0.7 s, 0.6 s, 0.4 s (Lake) |
| C, surface: `CatalogClaimBridge`, `SqlHoldsFacts`, `SqlHoldsRuns`, `SqlHolds`, `SqlSelectEval` | 1.8 s, 2.1 s, 2.2 s, 2.4 s, 1.6 s (Lake) |
| D, model: `RowwiseExpr`, `ExceptSubqueryRun`, `CorrelatedSubqueryRun`, `PlainInsertRows` | 1.3 s, 0.6 s, 0.6 s, 0.5 s (Lake) |
| D, surface: `PlainDeleteAnalysis`, `DeleteEffectCheck`, `DeleteFrameShape`, `DeleteFrameCheck`, `SelectOneWhere` | 1.9 s, 1.9 s, 1.8 s, 1.9 s, 1.9 s (Lake) |

The tables leave out a root module or a Lake file that only gets an
import or a module name. Time does not separate the forms.

## A false claim, and a claim outside the reach

- Each form: the claim is executable, so `decide` on a small database
  shows that a claim is false. The instance fixtures do this for the
  purge with `OR` and the claim with `AND`.
- Base and B: the proof of a false claim stops at a goal about rows
  that has no proof. A claim outside the reach has no law to apply, and
  no message says so.
- A: the proof of a false claim stops at a goal about rows. No claim is
  outside the reach of the statement language.
- C: the proof of a false claim stops at a goal about rows, after the
  tactic. For a claim outside its reach, the tactic names the part with
  no law, for example "`sql_holds` has no law for ORDER BY in the
  query". The fixture `PurgeTacticCases.lean` holds eleven such
  messages.
- D: `decide` reports that the check is false. It does not say which
  condition failed, and it does not separate a false claim from a claim
  outside the pattern. A diagnostic costs about 40 to 60 more lines.

The goals that `sql_holds` leaves are long. The goal of the effect
claim names the reached rows as `LiteralData.deleted` in the context of
the DELETE, and the filter as a resolved expression. The status file of
form C shows them.

## Which forms combine

- B replaces the base form. The retention fixtures prove the laws of
  the base form from the laws of B.
- C needs B. C makes the hand composition of B unnecessary for a claim
  in its reach, and the laws stay for a claim outside it.
- The data fact of A (`mem_deleted`) is a part of B and C. The helper
  of A states the rows that the purge leaves as an equivalence, with
  the filter over the bound values. Each proof of B and C derives one
  direction of it for its goal, from `Model.Database.rows_getD_setRows`,
  `LiteralData.mem_deleted` and `Resolved.Expr.Rowwise.evaluate_congr`.
  The effect proof uses that a row that is left was not selected. The
  frame proof uses that a row that is not selected is left. In form C
  these are 6 of the 7 lines after `sql_holds` in the effect proof, and
  about 8 lines in the frame proof. In form B the same steps are in the
  hand composition (`purge_clears`, `purge_keeps_rows`).
- The analysis and the send theorem of D (`PlainDelete.analyze`,
  `PlainDelete.ifOk_send`) do not depend on the checks. They replace
  the 43 helper lines that run the purge, for each schema. As a public
  theorem, `PlainDelete.ifOk_send` is a send rule for one kind whose
  premise gives the resolution to that kind. ADR 0033 (D6, D7) keeps no
  such rule. The same content fits the ADR as a step of `sql_run`: the
  tactic computes the resolution on the catalog of a hint and proves
  that the step continues from the kind rule and the data facts.
- A check of D can stand on the laws of B. The pilot built D on the
  base form, so this is not measured.

## Forms that the pilot left out

- An SMT solver for the conditions about rows. Lean has no solver
  bridge in its core, the core modules of the model import only `Init`,
  and the values of SQLite (affinity, collation, NULL) have no solver
  theory. The encoding needs its own proof.
- Bounded checks and property tests. They find a counterexample and
  prove nothing for each database. The repository has them: the
  `decide` instances and the conformance corpora. They help each form.
- A program logic for queries with its own judgments. Its content is
  the laws of form B.

## Recommendation

Use forms B and C as the way to prove a claim, with two parts of A and
D.

1. Claims stay SQL queries. A client and a reviewer read the same
   language as the statements, and the conformance evidence gives the
   claim its meaning. A proposition about rows stays possible as a
   statement, because the laws end in rows: form A is the lower level
   of form C, not a competitor.
2. The library has one law for each operator, as an equation or an
   equivalence (form B). The laws of one query form are deleted. This
   meets the owner goal of 2026-11-24 for the laws: general laws with
   many uses. The package code decreases by 61 lines before the tactic.
3. The tactic `sql_holds` applies the laws (form C). Form B alone moves
   the cost to each client: 71 proof lines for the frame claim. With
   the tactic the client writes the content of the claim: why a kept
   row stays, and why two rows that compare equal are one row.
4. Take from form A the exact rows that a write leaves, as a library
   fact for each write kind, stated with the bound values and not with
   the context of the statement. `sql_run` or `sql_holds` rewrites with
   it. Estimate: the effect proof goes from 7 lines to about 3 after
   the tactic.
5. Take from form D the analysis of a write, as a step of `sql_run`
   with the catalog as a hint: the tactic computes the resolution on
   the catalog, as `sql_holds` does for a claim, and proves that the
   step continues from the kind rule and the data facts. The site
   structure and its 43 helper lines for each schema go away. Estimate:
   each proof of form C loses most of its first 10 lines. The theorem
   `PlainDelete.ifOk_send` itself is not taken: it is a send rule for
   one kind, which ADR 0033 (D6, D7) does not keep. To keep it as a
   theorem needs an amendment of the ADR by the owner.
6. Do not build checkers for patterns of claim now. A checker gives the
   shortest client proof, 2 lines, but a pattern costs 76 to 163
   package lines, a claim outside the exact pattern is refused, and the
   refusal has no reason. A checker is right when many clients state
   one pattern. Then it is a thin layer over the laws of B.

With points 4 and 5, the estimate for a client is 2 to 3 statement
lines and 5 to 15 proof lines for each claim of the pilot, with no
helper. This estimate is not measured.

Limits of the recommendation:

- The reach of the tactic is small today: one top-level form, one
  table, row-wise expressions, `EXCEPT`. Joins, aggregates, `IN`,
  function calls and `count(*) = 0` need laws and cases. Each costs
  once, and the message of the tactic names the missing part.
- The tactic selects the laws in its code. `sql_select` has registered
  rules (ADR 0027). A design for the full form decides whether
  `sql_holds` uses a registered rule set, so that a new law needs no
  change of the tactic.
- The law of `EXCEPT` needs that two rows of its first term that
  compare equal are identical (`Resolved.equalRowsIdentical`). The
  tactic leaves this premise as a goal.
  `Resolved.equalRowsIdentical_rowidFirst` proves it for a valid table
  when column 0 of the table is the rowid alias and the first term
  selects that column first. The claims of the pilot meet both
  conditions with `SELECT *`. For another table or another list of
  columns the client proves the premise directly.

## Checks

On each branch, at its last Lean change: `just dev-build`,
`just test-full` and `just verdict` passed, local. One exception: on
form C, `just test-full` ran at `3c505c1d`, and `just dev-build` and
`just verdict` ran at `5bc3c323`, which changes one docstring line. `just test-full`
failed on the base form and on form A at a high machine load, with a
timeout of 120 s in `test_stateful_modes[True]` of
`tests/conformance_generation_test.py`, and passed when the load was
lower. `just test-nix` and `just test-scheduled-checks` run once on the
branch that the owner selects, before its pull request.
