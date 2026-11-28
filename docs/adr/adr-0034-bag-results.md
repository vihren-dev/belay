# ADR 0034: Query results as bags

Date: 2026-11-28. Status: PROPOSED. Audience: designers and reviewers.
Evidence: the [experiment findings](../../experiments/bag-results/README.md), the
[integration survey](../records/bag-results-integration-survey.md) and the
[task file](../../plans/20261128-bag-results-adr.task.md).
Related: [issue 489](https://github.com/vihren-dev/belay/issues/489) (the equivalence of two
scripts), [ADR 0017](adr-0017-user-surface.md) D3 (`Output.oneOf`),
[ADR 0018](adr-0018-surface-sql.md) D6 (the results that SQLite may give), the
[simplification goal](../development/lean-simplification-goal.md).

## Overview

SQLite promises the order of the rows of a query only where ORDER BY gives them different keys.
LIMIT and OFFSET then take rows that SQLite does not fix. The model gives the output of a query
as one list of rows (`Output.rows`) or as a choice between such lists (`Output.oneOf`). Where
SQLite promises no order, the list is in a normal form. The output does not record where SQLite
promises the order. So the model gives equal outputs to queries from which an application reads
different lists.

The owner proposed on 2026-11-28 that the rows of a result are a bag (a multiset), that ORDER BY
can make a list of a bag, and that LIMIT of a bag is a bag that is not determined. This ADR
adopts the proposal in two parts:

- **The bag module.** One directory of Lean files has all the definitions and laws of bags,
  ranked bags (tie groups in order) and choices. It imports only the Lean core library.
- **The integration.** The output of a query and of RETURNING is a ranked bag or a choice
  between ranked bags. The claims of the surface package read the ranked results, and helpers
  read the lists that the results permit. The evaluator of the model does not change: it
  computes the rows in the order of one plan, as today, and the bag module starts where the
  evaluator gives its result.

## Context

### What SQLite does

The probes (`experiments/bag-results/probes/`) ran on the pinned SQLite 3.51.0. Each probe runs
one query under two plans, or shows the plan. The probes show what one build does; they do not
show what SQLite promises.

| Probe | Query | Result |
| --- | --- | --- |
| P0 | `SELECT name` without ORDER BY, with `ORDER BY p` (a tie), with `ORDER BY name` | `bob, ada`; `bob, ada`; `ada, bob` |
| P1 | `LIMIT 1` without ORDER BY, rowid scan and index scan | `bob`, then `ada` |
| P3 | `ORDER BY p` with a tie, rowid scan and index on `(p, name)` | `bob, ada, cy`, then `ada, bob, cy` |
| P4, P5 | `DISTINCT name COLLATE NOCASE` and `GROUP BY` over `a`, `A` | `a`, then `A`: the plan selects the row that stays |
| P6 | `group_concat(name)` | `bob,ada,cy`, then `ada,bob,cy` |
| P7 | `sum`, `total`, `avg` of `1e308, 1e308, -1e308` | `Inf` for all three, then `1.0e+308`, `1.0e+308` and `3.33333333333333e+307` |
| P16 | `sum` of `MAX_INT, 1, -1` | `integer overflow`, then `9223372036854775807` |
| P9 | a CTE with LIMIT that the query reads two times, with each materialization hint | one materialization in all three forms |
| P10 | a scalar subquery with LIMIT, uncorrelated and correlated | evaluated once; evaluated for each outer row |
| P11 | a scalar subquery with ORDER BY | the first row of the order |
| P12, P13 | ORDER BY in a FROM subquery | the outer query keeps the order; in a join, SQLite ignores it |
| P15 | `1 IN (SELECT x … ORDER BY abs(-9223372036854775808))` | `integer overflow` for a column; `1` for the rowid |

### What the model does now

`Output` (`Shared/Execution/Output.lean` of the model package) has the constructors `rows`,
`done`, `error`, `oneOf` and `unmodeled`. `Query.possibleResults`
(`Queries/Evaluation/PossibleResults.lean`) lists the results that SQLite may give (ADR 0018,
D6): it puts each tie group of the ORDER BY terms in normal form (`Resolved.normalForm`), joins
the groups into one list, and lists each choice of a group that LIMIT or OFFSET cuts.
`Output.ofResults` gives `Output.rows` for one result and `Output.oneOf` for two or more
different results.

The experiment `CurrentOutputs.lean` proves with `decide +kernel` that the model gives the same
results, one list `ada, bob`, for the three queries of P0. Native SQLite gives `bob, ada` for
the first two. So:

- A relation that compares outputs, as the one that issue 489 needs, cannot tell a query without
  ORDER BY from a query with ORDER BY.
- A claim `returnsResult (· = [[ada], [bob]])` about the query without ORDER BY is provable. An
  application that reads the rows in order can get `bob, ada`. The documentation says that the
  rows are in normal form, so the claim is about the normal form, not about the rows that the
  application reads.
- Laws about results state facts about sorted lists. Two laws connect the normal form with
  permutations: `normalForm_perm` (the normal form is a permutation of its rows), which the
  window proofs use, and `normalForm_eq_iff_perm` (two normal forms are equal exactly when the
  rows are permutations of each other), which one test uses.

The model already refuses some results that depend on an order (`docs/semantic-subset.md`):

- a FROM subquery whose row multiset depends on the tie order of a window;
- a scalar subquery or an IN window over ties, unless every permitted order gives the same
  values;
- a `SELECT DISTINCT` whose equal rows differ.

A column outside an aggregate reads the first row of the group in the order of the source.
`group_concat` joins its values in the order of the group's rows, and `sum` and `total` fold
them in that order (`Queries/Evaluation/Summation.lean`). Probes P6, P7 and P16 show that
SQLite can give other results for other plans. The SQLite documentation says that the order of
`group_concat` is arbitrary without an ORDER BY argument
([aggregate functions](https://sqlite.org/lang_aggfunc.html)), and that the rows of RETURNING
appear in an arbitrary order ([RETURNING](https://sqlite.org/lang_returning.html)).

### What the harness and the judge do

The judge (`judge/outputs.py`) compares a result without ORDER BY and LIMIT as a bag, and a
result with ORDER BY or LIMIT by the native tie groups, each group as a bag. The prediction is
the first result of the model, in the order of the evaluator. `Output.oneOf` never reaches the
judge. The corpora store only native evidence (the survey). So this ADR changes neither the
judge, nor its lock, nor a corpus.

### The prototype

`experiments/bag-results/Bags/` defines the module with the Lean core library only and proves
its laws without `sorry`. The experiment's Nix build checks that each audited theorem depends
only on `propext`, `Classical.choice` and `Quot.sound`.

- `ND α := α → Prop`, the values that a nondeterministic program can give, with a lawful
  monad.
- `Bag α`, the quotient of lists by permutation, with `map`, `filter`, UNION ALL (`++`) and
  `product`, and their laws: for example `filter_append`, `append_comm` and `filter_product`.
  Equality of bags is decidable with `List.isPerm`.
- `Bag.sample o b`, the sample of a bag: its rows sorted by a total, transitive and
  antisymmetric order `o` (`SortOrder`), with the insertion sort of the model. Two bags are
  equal if and only if their samples are equal (`sample_eq_iff`), so equality can also be
  decided through the samples (`Bag.decEqBySample`). The sample is a sorted list, not an order
  that SQLite promises.
- `Bag.arrange b : ND (List α)`, the lists of the rows of `b` in each order. It is the one
  source of nondeterminism: each choice is a list function after an arrangement.
- `Bag.take n`: the sub-bags whose size is the smaller of `n` and the size of the bag
  (`take_iff`).
- `Bag.distinct`: the row that stays for each class of a collation is a choice; when the
  collation is equality on the rows, the result is determined (`distinct_deterministic`).
- `Ranked α := List (Bag α)`, tie groups in order; ORDER BY (`rank`) by a total preorder. The
  ranked result does not depend on the order of the input (`rank_deterministic`), and its rows
  are the input bag (`toBag_rank`).
- `Ranked.window`, OFFSET and LIMIT over ranked rows: its lists are the slices of the lists of
  the ranking (`window_arrange`). For SQLite's integers, a negative LIMIT is no limit and a
  negative OFFSET is 0. Without ORDER BY, the window keeps any sub-bag of a determined size
  (`window_sqlite_ofBag_iff`).
- `Ranked.canon`, the canonical form: two ranked results permit the same lists if and only if
  their canonical forms are equal (`arrange_eq_iff_canon`).
- `Equivalent`, the equivalence of two results by the lists that they permit. For results whose
  every value is one bag, it is equality of the sets of bags (`equivalent_unordered`).

The [findings](../../experiments/bag-results/README.md) list the theorems.

### Cost of a quotient in the kernel

The Nix build of the experiment measured `decide +kernel` on two orders of the same rows of two
integers in three ways: as a quotient with the decision of `List.Perm` (`Quotient.decidableEq`),
as a quotient whose decision compares the samples of the two bags (their rows in the model's
normal form, through `Quotient.lift`), and as normal-form lists. The times are the best of three
runs, without the time of the imports and the definitions.

| Rows | `List.Perm` | Samples | Normal form |
| ---: | ---: | ---: | ---: |
| 10 | 0.03 s | 0.04 s | 0.04 s |
| 50 | 0.8 s | 0.7 s | 0.7 s |
| 100 | 3.3 s | 2.5 s | 2.4 s |
| 200 | 13.3 s | 9.4 s | 9.1 s |

All three are quadratic. For 100 and 200 rows, the decision by `List.Perm` costs about 1.4 times
the normal form. The decision through samples computes the normal forms of a list of each bag
and compares them, the same work as the comparison of normal-form lists. In the cited build, it
took 3% more time for 100 rows (2.507 s against 2.428 s) and 2% more for 200 rows (9.359 s
against 9.144 s); in two earlier builds of the experiment, the two were within 2% of each other
(findings). So for this benchmark, one equality of two bags, the quotient with samples costs
about as much as normal-form lists.

## Decision

### D1. The meaning of a result

The result of a query is a value of `ND (Ranked (List Value))`: the ranked results that SQLite
may give.

- A query without ORDER BY has one tie group: a bag.
- ORDER BY splits the rows into tie groups by its keys, in order. A total order gives groups of
  one row.
- LIMIT and OFFSET keep a sub-bag of the right size of each group that they cut, as one
  group, because SQLite promises no order for its rows either (`Ranked.window`).
- DISTINCT and GROUP BY under a collation can keep different rows for different plans (P4 and
  P5). The model refuses such a DISTINCT and reads the first row in the order of the source for
  GROUP BY, and this ADR keeps these rules (see "Not decided here").

An application reads one list. The lists that a result permits are the arrangements of its
groups, in order (`Ranked.arrange`). Two results are equivalent when they permit the same lists.

### D2. The place of the bag module

The module is the directory `Belay/Sqlite/Model/Bags/` of the model package, with the namespace
`Belay.Sqlite.Model.Bags`. Its files import only the Lean core library and other files of the
directory. A Python test in `tests/` checks the imports of the directory.

A separate Lake package would make the boundary a part of the build graph. It would also need
its own Nix derivation (`build-support/default.nix`) and an entry in the requirements and the
shared libraries of each package that builds on the model. The import test gives the same
boundary for less supporting code (owner decision 1).

### D3. The interface of the module

The module has the definitions and laws of the prototype, without its examples (`Select.lean`
and `Examples.lean`). The model also needs:

- **Enumerations.** Each choice also has a function that computes its results. It takes a list
  of the rows: without a sort order, a list of results cannot be a function of the bag alone,
  because its order would depend on the arrangement. The list of the evaluator then fixes the
  order of the enumeration. ORDER BY has `rankLists le l : List (List α)`, the
  tie groups of `l` as lists (the sort of `l` by `le`, split into tie groups), with the law
  `rank le (Bag.ofList l) = pure ((rankLists le l).map Bag.ofList)` for a total and transitive
  `le`. LIMIT has `subBagsOf n l : List (Bag α)`, the results of LIMIT `n` on the rows of `l`,
  with the membership law `c ∈ subBagsOf n l ↔ (Bag.ofList l).take n c`. The window of ranked
  rows takes its groups as lists, and the rows that `distinct` can keep have an enumeration
  too. The model computes with them on the lists of its evaluator, and the claims use the
  meaning through the membership laws. The order of an enumeration does not change an output,
  because `Output.ofResults` sorts the results (D5). For a type with a sort order, an
  enumeration can also take a bag through its sample, for example
  `subBagsOf n (b.sample o)`: its order of results is then a function of the bag. The model
  needs only the versions that take lists, because its evaluator gives lists.
- **Sample.** The prototype has it (`Bag.sample`, `SortOrder`, `Bag.decEqBySample`), with the
  insertion sort of the model and its laws (`stableSort`). The module takes the sort from the
  prototype, and slice 2 replaces the model's copy of the sort and its laws with it, so the
  sort exists once.
- **Canonical form.** The prototype has it: `Ranked.canon` removes empty groups and splits a
  group whose rows are all equal into groups of one row. Two ranked results permit the same
  lists exactly when their canonical forms are equal. The model uses it for `Output.ofResults`
  (D5). Equality of canonical forms is decidable, and the kernel can decide it.

The module has no SQLite content other than the rules for a negative LIMIT and OFFSET
(`sqliteLimit`, `sqliteOffset`): no `Value`, no collation and no SQL syntax. A collation enters
as an argument, for example the equivalence of `distinct` or the key order of `rank`.

### D4. The representation of bags in the model

Bags are the quotient `Bag`, not normal-form lists (owner decision 2). The laws of bags then
come from the quotient, and no law needs a sort.

The model uses the sample of a bag of rows with the order of `Resolved.compareRows`, the order
of `Resolved.normalForm`. The sample of a bag is the normal form of each list of the bag. The
model uses it in two ways:

- **Equality.** The model declares `Bag.decEqBySample` as the instance for bags of rows, with a
  higher priority than the decision by `List.Perm`. In the benchmark, `decide +kernel` then
  costs about as much as for normal-form lists. For 100 rows: 2.507 s through samples,
  2.428 s for normal-form lists, and 3.276 s by `List.Perm`.
- **One list to show.** `#eval` display (`OutputRepr`), the `outputJson` functions of the
  tests, `ToExpr` for the counterexample replay, and the text of each choice in checked SQL
  documentation blocks show the sample of each group.

The sample is not an order that SQLite promises. The claims that the surface package defines
(D7) do not read it. A property that a user gives to `returnsResult` can read it: such a claim
is about the sorted rows, while `returnsLists` states a fact about each order that SQLite may
give. In the module, the docstring of `Bag.sample` says this; in the prototype, the module
docstring of `Bags/Sample.lean` says it.

### D5. The output of a statement

`Output.rows` and `Output.oneOf` carry ranked results:

- `Output.rows (result : Ranked (List Value))`: one ranked result. The model puts it in
  canonical form.
- `Output.oneOf (results : List (Ranked (List Value)))`: two or more ranked results with
  different canonical forms.

`Output.ofResults` takes the canonical form of each result, removes duplicates, and sorts the
results by a fixed order: group by group, each group by its sample (D4) with
`compareResults`, and a ranking that is a prefix of another one first. So the output does not
depend on the order in which the model finds the results, as today. The rows of RETURNING are one bag, because the SQLite documentation gives them an
arbitrary order; the model today puts them in normal form. `Output.done`, `error` and
`unmodeled` do not change.

The evaluator does not change. `Query.possibleResults` starts, as today, from the records of the
evaluator (`Query.uniqueRecords`: each result row with its sort keys), before the window and the
projection. The sort keys can be absent from the result rows, so the ranking cannot start from
`Query.results`. It computes the tie groups of the records by the ORDER BY terms as lists with
`rankLists`, and the law of D3 connects them with `rank`. It takes the window enumeration of
these groups and maps each record to its result row (`Ranked.map`). `rank` and `rankLists`
need a total and transitive order; the model has `compareSort_transCmp` for its order of sort
keys. This replaces `tieGroups`, `choose`, `groupChoices`, `windowChoices` and the use of
`normalForm` for results. The prediction for the judge stays the list of the evaluator
(`Query.results`), so the verdicts should not change; slice 2 checks this (D9). The second path
of the conformance runner (`PossibleOutputs.lean`) checks that the native rows are a list that a
possible result permits.

### D6. What an application reads, and equivalence

The model package defines, with the module:

- `Output.Permits output rows`: an application can read `rows` from `output`. For
  `Output.rows r` and `Output.oneOf rs`, this is an arrangement of `r` or of a result in `rs`.
  For `Output.done`, `error` and `unmodeled`, it is false.
- `Output.Equivalent a b`: the two outputs are equal, or both return rows and permit the same
  lists.

Equal outputs are equivalent. The converse is false for choices: the one result `[{a, b}]` and
the two results `[{a}, {b}]` and `[{b}, {a}]` permit the same two lists, but their canonical
forms differ. The experiment proves this example (`equivalent_but_canonical_results_differ`).
A proof of equivalence for such outputs uses the laws of the module, not `decide`.

The equivalence of two scripts for issue 489 compares their last outputs with
`Output.Equivalent`. This ADR does not define the relation on scripts; it gives the relation on
outputs that it needs.

### D7. The claims of the surface package

Today `Output.returnsResult property` holds when `property` holds for the rows of
`Output.rows`, or for each listed result of `Output.oneOf`. Its property reads a list, and it is
decidable when the property is. The new claims are:

- **The primitive.** `returnsResult (property : Ranked (List Value) → Prop)` holds when the
  output returns rows and `property` holds for each possible ranked result. It is decidable when
  the property is. A property can read the tie groups, the bag of all rows, or the lists that
  the result permits.
- **Sugar over the primitive.** Each helper is a `returnsResult` with a fixed property, so no
  helper is the only way to state a claim:
  - `returnsLists P`: `P` holds for each list that the output permits. Its decision enumerates
    the arrangements of each group, so `decide` suits it only for small results.
  - `returnsBag rows`: each possible result has the bag of `rows`.
  - `returnsRows P`, `Holds` and `Empty` read the bag of rows: each row has `P`, a row exists,
    no row exists. Their meaning does not change.
- **Programs.** `query` changes only for the outputs that return rows. For `Output.rows` and
  `Output.oneOf`, it gives one list that the output permits: the groups of the first result in
  the order of `Output.ofResults`, in order, each group as its sample (D4). Today `query` gives the
  first listed result. As today, `done` gives `.ok []`, an error gives `.error code`, and
  `unmodeled` ends the run before a program gets a value. `single` applies `singleValue` to the
  value of `query`, as today. So a program that `query` runs can depend on an order that SQLite
  does not promise, as it can today. A claim that holds for each order uses `returnsLists`, not
  `query`.
- The bridges from `∀ result ∈ bound.possibleResults …` to claims, `OutputChoice`, `Succeeds`,
  `sql_select` and `sql_run` read ranked results.

A property of the permitted lists is the claim of an application, but its decision grows with
the factorial of the size of a group. The primitive therefore reads the ranked result, and the
list view is a helper over it (owner decision 3).

### D8. Slices

One task file and one status file cover the two slices.

| Slice | Content |
| --- | --- |
| 1 | The bag module in the model package (D2, D3), from the prototype, with the import test. No other code changes. |
| 2 | `Output` and `Query.possibleResults` over ranked results (D5), RETURNING, `Output.Permits` and `Output.Equivalent` (D6), the claims (D7), and all callers in the model, the surface package, the conformance package and the tests. Slice 2 also replaces the model's insertion sort and its laws with the module's (D3). Each commit that changes what a user sees updates its documentation in the same commit: `docs/semantic-subset.md`, the package README, the guide and the README examples that show outputs. A model test states the outputs of the three queries of P0. |

Slice 2 is large, because a change of the type of `Output` breaks all its callers at once and
the project keeps no compatibility path. Each commit of the slice builds.

**The experiment.** The findings, the probes and their script stay in `experiments/bag-results/`
as the evidence of this ADR; the probes need only native SQLite. Slice 1 deletes `Bags/`,
which becomes the module. After this deletion, `nix-build experiments/bag-results/default.nix`
no longer audits the theorems of the prototype. So the commit that deletes `Bags/` also writes
into the findings the last revision at which this build replays all of the evidence.
`CurrentOutputs.lean` reads the outputs that slice 2 changes, so slice 2 deletes it, its model
test of P0 replaces it, and the experiment's Nix build keeps only the probes and the kernel
cost.

### D9. What each slice shows

- **Slice 1.** The module builds with no `sorry`, and its audited theorems use only the three
  standard axioms. The import test passes. The verdict of each corpus is the same as at the start
  of the slice.
- **Slice 2.** The verdict of each corpus is the same as at the start of the slice, because the
  prediction does not change. The model test of P0 shows that the query without ORDER BY and the
  query with the tied `ORDER BY p` have equal outputs, one group `{ada, bob}`, and that the query
  with `ORDER BY name` has a different output, two groups. The tests that claimed an order for a
  result without ORDER BY are either restated as claims on bags or removed with the reason in the
  status file. The status file lists them. The checked documentation builds.

Each slice records the code lines with the counter of the simplification goal, at its start and
end revisions: the full total of the goal's scope, and the packages, the tests and the other
maintained Lean code, such as the experiment, separately.

### D10. Line budget and capability effects

Code lines are the `Code` field of scc 3.7.0, the counter of the simplification goal.

- **Replaced.** The enumeration and normal-form code that the module replaces has 431 code
  lines (733 `wc -l` lines, survey). Slice 2 also deletes the model's copy of the insertion sort
  and its laws, which the module has (about 58 code lines in the prototype).
- **Added.** The prototype has 1,322 code lines, and 1,261 without its examples `Select.lean`
  and `Examples.lean` (findings). Slice 1 adds about 1,261 lines plus the enumerations and
  their membership laws.
- **Net.** The module is about three times as large as the code that it replaces, because it
  proves general laws that the model does not have today, for example the canonical form and
  its uniqueness (208 code lines). The ADR expects a net increase of about 770 to 1,020 code
  lines of the packages after slice 2, plus the change of the tests, which slice 2 measures.
  Laws of the model that sort today can become shorter with the module, but the ADR does not
  count on that. Slice 2 records the measured result.
- **Full scope.** The goal also counts the experiment. Its 1,343 code lines come in the pull
  request of this ADR, before the ADR, and the slices delete them. So from the revision before
  the experiment (`1fb455ac` on main) to the end of slice 2, the full scope grows by the same
  770 to 1,020 lines and the change of the tests: about 1% of the last recorded count of the
  goal (98,829 lines, ADR 0033). From the revision with the experiment, it shrinks by about 320
  to 570 lines, plus the change of the tests. The line budget (owner decision 5) is the growth
  from the revision before the experiment, because the Lean files of the experiment are
  temporary.

The increase is not temporary, because the module stays, and it moves the count further from
the limit of the goal (45,000 lines). The ADR recommends it, because the module gives the
meaning of results that the model states today only through normal forms (owner decision 5).

Capability groups of the simplification goal:

- **M07** (ordering and LIMIT/OFFSET alternatives) is retained and gains the tie groups in the
  output.
- **M03** (RETURNING) is retained: the rows are a bag instead of a normal-form list.
- **S04** (claims over every database) and **S06** (complete-execution equivalence): a claim
  that a result without ORDER BY is one sorted list stops being provable, because SQLite does not
  promise it. The ADR's view is that this restores SQLite semantics, which the goal makes
  mandatory, and that the capability stays, because each such claim has a restatement on bags.
  Slice 2 lists each affected test with its restatement (owner decision 4).

## Consequences

- **Outputs say what SQLite promises.** An output records its tie groups, and the equivalence
  of outputs follows what an application can read.
- **Laws without sorting.** A law that ignores the order of rows is a law of the quotient, for
  example that WHERE commutes with UNION ALL.
- **Claims on order need ORDER BY.** A claim that reads the order of rows of a query without
  ORDER BY has a proof for each order, or is stated on the bag.
- **Comparable kernel time in the benchmark.** With the decision through samples, one
  equality of two bags of rows costs about as much as the equality of normal-form lists. In
  the cited build, it took 3% more time for 100 rows and 2% more for 200 rows.
- **No judge change.** The judge already compares bags and tie groups, and the prediction does
  not change.

## Alternatives considered

**Normal-form lists with explicit tie groups.** `Output.rows` could carry a list of groups, each
in normal form. This is the canonical form as data. In the benchmark, its kernel cost is about
the same as for the quotient with the decision through samples, and 0.7 times the cost of the
decision by `List.Perm`, for 100 or more rows. Each law of bags would then need a sort and
`normalForm_eq_iff_perm`, and the type would not stop a claim from reading the order of the
normal form. The quotient gives these laws directly, and its sample gives about the same
kernel cost in the benchmark.

**Only the meaning, without enumerations.** The module could define the choices only as values
of `ND`. The model could then not compute outputs, and the tests could not decide them.

**A separate Lake package.** See D2.

**A new evaluator on bags.** The evaluator could compute with bags from the start. The order of
the evaluator is the plan of the model: the prediction, `group_concat` and the aggregates read
it. A change would change predictions and verdicts, for no gain in the meaning of the output.

## Not decided here

- **Order-dependent aggregates.** `group_concat`, `string_agg`, the JSON group aggregates, the
  REAL sum of `sum`, `total` and `avg`, and the overflow of an integer `sum` depend on the order
  of the rows (P6, P7, P16). The model gives the result for the order of the evaluator. The
  module's `Bag.aggregate` gives the meaning, but an enumeration of all orders grows with the
  factorial of the number of rows. A later ADR decides.
- **The row that DISTINCT and GROUP BY keep.** Under a collation, the plan selects the row
  (P4, P5). The module's `Bag.distinct` gives the meaning; the model keeps its rules.
- **Errors that depend on the plan.** A sort key that fails gives an error for one plan and a
  value for another (P15). The model keeps its rules for errors.
- **Choices inside subqueries.** The model refuses ambiguous scalar and IN subqueries, and FROM
  subqueries whose multiset depends on a window. The module makes choices for them possible:
  for example, one choice for each evaluation of a correlated subquery (P10). A later ADR decides
  whether choices are shared or independent, for example for a CTE that a query reads two times
  (P9).
- **The order of a FROM subquery.** SQLite keeps the order of a FROM subquery for the outer
  query in some cases (P12) and ignores it in others (P13). The model reads the rows of the
  subquery in the order of its evaluator, as today.
- **The reduction of scripts to queries** (issue 489). It uses D6.

## Owner decisions

1. **Place of the module.** A directory of the model package with an import test (D2,
   recommended), or a separate Lake package.
2. **Representation.** The quotient `Bag`, with its equality for rows decided through samples
   (D4, recommended), or normal-form lists with tie groups.
3. **The primitive claim.** `returnsResult` reads the ranked result, with the list view as the
   helper `returnsLists` (D7, recommended), or `returnsResult` reads the permitted lists, and
   `decide` enumerates the arrangements of each group.
4. **Capability accounting.** Claims that a result without ORDER BY is one sorted list are
   restated on bags, and S04 and S06 count as retained (D10, recommended), or they count as a
   loss that the owner approves.
5. **Line budget.** Accept a net increase of the goal's full scope of about 770 to 1,020 code
   lines and the change of the tests, from the revision before the experiment (`1fb455ac` on
   main) to the end of slice 2 (D10, recommended), or integrate a smaller module first: for
   example, without the uniqueness of the canonical form (`CanonicalUnique.lean`, 123 code
   lines), which only the equivalence of outputs (D6) needs, and add it with the work on
   issue 489.
