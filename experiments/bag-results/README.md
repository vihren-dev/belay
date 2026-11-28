# Findings: query results as bags

Date: 2026-11-28. Audience: designers and reviewers.
Task: [`plans/20261128-bag-results-adr.task.md`](../../plans/20261128-bag-results-adr.task.md).
ADR: [`docs/adr/adr-0034-bag-results.md`](../../docs/adr/adr-0034-bag-results.md).
Survey: [`docs/records/bag-results-integration-survey.md`](../../docs/records/bag-results-integration-survey.md).

This directory holds the experiments for the ADR of query results as bags: a prototype of the
bag module, a proof of what the model gives now, native SQLite probes, and a measurement of the
kernel cost of two representations of a bag.

## How to reproduce

```console
nix-build experiments/bag-results/default.nix
```

The build uses the pinned Lean toolchain, the pinned model package and the pinned SQLite 3.51.0.
It compiles each Lean file in import order and fails on a warning or an error, so a `sorry`
fails it. Each `#print axioms` line names an audited theorem; the build fails when such a
theorem depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. Then it
runs the probes, requires exit status 1 of `sqlite3` (probes P15 and P16 end with a runtime
error), compares their output with `probes/probes.expected`, and measures the kernel cost. The output directory has:

| File | Content |
| --- | --- |
| `proofs.json` | the axioms of each audited theorem, by module |
| `*.log` | the compiler output of each module |
| `kernel-cost.json` | the kernel times of `kernel_cost.py` |
| `lines.json` | the code lines of the Lean files, for each file (`scc --by-file`) |
| `model-path.txt`, `toolchain-path.txt`, `sqlite-path.txt` | the pinned store paths |

The results below are from the Nix build
`/nix/store/zhfh5aq45zr0qrzkcr5bmcy5y6hz7cci-bag-results-experiments`.

## Current outputs of the model

`CurrentOutputs.lean` evaluates three queries of the guide's `customers` table with the pinned
model package (`PossibleResultsExamples.possible`):

- `SELECT name FROM customers` (`unordered`);
- `SELECT name FROM customers ORDER BY p`, where both rows have the same `p` (`tied`);
- `SELECT name FROM customers ORDER BY name` (`byName`).

`decide +kernel` proves that the three give the same results, `[[ada], [bob]]`
(`unordered_eq_byName`, `tied_eq_byName`), and that `Output.ofResults` gives the same output for
them (`outputs_equal`). Native SQLite gives `bob, ada` for the first two queries and `ada, bob`
for the third (probe P0). So the output does not record which order SQLite promises.

## Native probes

`probes/probes.sql` runs on the pinned SQLite 3.51.0, and `probes/run-probes.sh` compares the
output with `probes/probes.expected`. Each probe runs one query under two plans (`NOT INDEXED`
and `INDEXED BY`), or shows the plan with `EXPLAIN QUERY PLAN`. The probes show what one build
does for one or a few plans. They do not show what SQLite promises; the ADR cites the SQLite
documentation for that.

| Probe | What it runs | What the build gives |
| --- | --- | --- |
| P0 | the queries of `CurrentOutputs.lean` | `bob, ada`; `bob, ada`; `ada, bob` |
| P1 | `LIMIT 1` without ORDER BY | `bob` for the rowid scan, `ada` for the index scan |
| P2 | rows without ORDER BY and with ORDER BY | `bob, ada, cy` and `ada, bob, cy` |
| P3 | `ORDER BY p` with a tie of two rows | `bob, ada, cy`, then `ada, bob, cy` |
| P4 | `DISTINCT name COLLATE NOCASE` over `a`, `A`, `b` | `a, b`, then `A, b` |
| P5 | `GROUP BY name COLLATE NOCASE` over the same rows | `a\|2`, then `A\|2` |
| P6 | `group_concat(name)` | `bob,ada,cy`, then `ada,bob,cy`; with `ORDER BY name DESC` in the aggregate, `cy,bob,ada` |
| P7 | `sum`, `total`, `avg` of `1e308, 1e308, -1e308` | `Inf` for all three, then `1.0e+308`, `1.0e+308`, `3.33333333333333e+307` |
| P8 | `sum` of `1e16, 1, -1e16, 1` | `2.0` for both plans |
| P9 | a CTE with `LIMIT 1` that the query reads two times, with each materialization hint | `ada\|ada`; the plan materializes the CTE one time in all three forms |
| P10 | a scalar subquery with `LIMIT 1`, uncorrelated, then correlated | the uncorrelated subquery runs one time (`ada` for each row); the correlated one runs for each outer row (`ada`, `bob`, `ada`) |
| P11 | a scalar subquery with ORDER BY | the first row of the order: `ada`, then `cy` |
| P12 | ORDER BY in a FROM subquery of one source | the outer `group_concat` and the outer rows follow the order of the subquery |
| P13 | ORDER BY in a FROM subquery that is part of a join | the outer rows do not follow it: `ada, bob, cy` for `ORDER BY name DESC` |
| P14 | ORDER BY in an IN subquery and an EXISTS subquery | the results do not depend on it |
| P15 | `1 IN (SELECT … ORDER BY abs(-9223372036854775808))` | `integer overflow` for a column without an index; `1` for the rowid, where the plan does not compute the key |
| P16 | `sum` of `9223372036854775807, 1, -1` | `integer overflow` for the rowid scan, `9223372036854775807` for the index scan |

## Prototype of the bag module

`Bags/` is a prototype of the bag module. It imports only the Lean core library and no model
code, and it proves its laws for any type of rows. The namespace is `BagResults`. Each audited
theorem has a `#print axioms` line after it; the Nix build records the axioms of each in
`proofs.json`.

| File | Content |
| --- | --- |
| `ND.lean` | `ND α := α → Prop`, the results that SQLite may give, with a lawful monad |
| `Bag.lean`, `Algebra.lean` | `Bag α`, the quotient of lists by permutation; `map`, `filter`, UNION ALL (`++`), `product`, `card`, membership, decidable equality; their laws |
| `Arrange.lean` | `Bag.arrange b : ND (List α)`, the lists of the rows of `b` in each order: the one source of nondeterminism |
| `Choice.lean` | LIMIT without ORDER BY (`Bag.take`), sub-bags (`Bag.Sub`), and aggregates that read an order (`Bag.aggregate`) |
| `Distinct.lean` | DISTINCT under a collation (`Bag.distinct`): the first row of each class in an arrangement |
| `Ranked.lean`, `TieGroups.lean`, `Rank.lean` | `Ranked α := List (Bag α)`, tie groups in order; the lists that a ranking permits (`Ranked.arrange`); ORDER BY (`Ranked.rank`) by a total preorder |
| `Slice.lean`, `Window.lean`, `SqliteWindow.lean` | OFFSET and LIMIT on lists (`slice`) and over ranked rows (`Ranked.window`); SQLite's integer OFFSET and LIMIT (`sqliteOffset`, `sqliteLimit`) |
| `Canonical.lean`, `CanonicalUnique.lean` | the canonical form of ranked rows (`Ranked.canon`) |
| `Equivalence.lean` | the lists that an application can read (`observe`) and the equivalence of two results (`Equivalent`) |
| `Select.lean` | a single-table SELECT, as an example of composition: WHERE, ORDER BY on the input rows, the window, then a total projection |
| `Examples.lean` | `decide +kernel` and `decide` on equalities of small literal bags |

The theorems for the points of the task file:

- **The algebra of bags.** `Bag.filter_filter`, `Bag.map_map`, `Bag.filter_map`,
  `Bag.filter_append`, `Bag.map_append`, `Bag.append_comm`, `Bag.append_assoc`,
  `Bag.card_filter_le`, `Bag.filter_product`, `Bag.filter_product_left`,
  `Bag.filter_product_right` and `Bag.card_product`.
- **LIMIT and OFFSET without ORDER BY.** `Bag.take_iff`: a result of LIMIT `n` is a sub-bag with
  `min n (card b)` rows, and each such sub-bag is a result. `Ranked.window_ofBag_iff` and
  `Ranked.window_sqlite_ofBag_iff`: with OFFSET, the result is a sub-bag of the bag with a
  determined number of rows; for SQLite's integers, a negative LIMIT is no limit, and a negative
  OFFSET is 0. `Bag.card_take` and `Ranked.card_window_sqlite` state the determined number of
  rows alone. `Bag.take_take` composes two limits, and `Bag.filter_take_not_comm` shows that
  WHERE and LIMIT do not commute.
- **ORDER BY.** `Ranked.rank_deterministic`: for a total and transitive order, ORDER BY gives
  one ranking, whatever the order of its input. `Ranked.toBag_rank`: the rows of each ranking
  are the input bag, so a reader that is a function of the bag of rows cannot see an ORDER BY
  without LIMIT. `Ranked.rank_arrange_of_all_tie` and `Ranked.observe_rank_trivial`: when all
  rows tie, the ranking permits each order of the rows.
- **OFFSET and LIMIT over ranked rows.** `Ranked.window_arrange`: the lists that the window
  permits are the slices of the lists that the ranking permits. A group that the window cuts on
  both sides keeps a sub-bag (`Bag.take_bind_arrange`). `Ranked.card_window_sqlite` applies
  SQLite's rules for negative values.
- **Canonical form.** `Ranked.arrange_eq_iff_canon`: two rankings permit the same lists if and
  only if their canonical forms are equal. `Ranked.canon` drops empty groups and splits a group
  whose rows are all equal into groups of one row (`Ranked.arrange_equal_rows` shows why).
- **Equivalence.** `equivalent_unordered`: two results whose every value is one tie group (a
  bag) are equivalent if and only if they permit the same bags. `equivalent_pure_iff`: two
  deterministic rankings are equivalent if and only if their canonical forms are equal.
  `equivalent_but_canonical_results_differ`: the result `[{a, b}]` and the choice between
  `[{a}, {b}]` and `[{b}, {a}]` are equivalent, but the sets of their canonical forms differ.
  So a comparison of outputs by data is sufficient for equivalence, but not necessary.
- **DISTINCT.** `Bag.distinct_deterministic`: DISTINCT is deterministic when the collation is
  equality on the rows of the bag. Under NOCASE, `a` and `A` are one class, and the row
  that stays is a choice (probe P4).
- **Aggregates.** `Bag.aggregate_of_perm`: an aggregate that gives equal results for each order
  of its rows is deterministic.

The Nix build audited 57 theorems: 53 of the prototype and 4 of `CurrentOutputs.lean`. 24
depend on `propext`, `Classical.choice` and `Quot.sound`, 31 on `propext` and `Quot.sound`, and
2 on no axiom (`Bag.arrange_nonempty` and `equivalent_equivalence`).

## Kernel cost of two representations

`kernel_cost.py` writes one Lean file for each case. Each file proves with `decide +kernel` that
the rows `row 0, …, row (n-1)` and the same rows in reverse order give equal bags. The rows have
two integer values, and the first value repeats, so the rows have ties. The two representations
are:

- **quotient**: `Quotient (List.isSetoid (List Value))`, decided with `Quotient.decidableEq` and
  `List.decidablePerm`;
- **normal form**: equality of `Resolved.normalForm` of the model, an insertion sort by
  `Resolved.compareRows`.

Each time is the best wall time of three runs, minus the best wall time of a baseline file with
the same imports and definitions but no proof (0.210 s).

| Rows | Quotient | Normal form | Quotient / normal form |
| ---: | ---: | ---: | ---: |
| 10 | 0.030 s | 0.036 s | 0.8 |
| 50 | 0.819 s | 0.634 s | 1.3 |
| 100 | 3.297 s | 2.378 s | 1.4 |
| 200 | 13.250 s | 9.088 s | 1.5 |

Both representations are quadratic in the number of rows. The quotient costs about 1.4 to 1.5
times the normal form for 100 and 200 rows; for 10 rows the two are equal within the noise.

## Code lines

The Nix build counts the code lines of the Lean files with scc 3.7.0, the counter of the
[simplification goal](../../docs/development/lean-simplification-goal.md) (`lines.json`, the sum
of the `Code` field): 1,246 lines in 18 files. `CurrentOutputs.lean` has 21 of them, and the
prototype `Bags/` has 1,225 in 17 files. The largest files are `CanonicalUnique.lean` (123),
`SqliteWindow.lean` (110), `Rank.lean` (102) and `TieGroups.lean` (102).

The simplification goal counts the code under `experiments/` as maintained code. Slice 1 of the
ADR moves the prototype into the model package as the bag module and deletes `Bags/`. Slice 2
deletes `CurrentOutputs.lean`, which a model test of P0 replaces, and keeps only the probes and
the kernel cost in this Nix build. The findings, the probes and their script stay as the
evidence of the ADR (ADR 0034, D8), and the findings then name the revision at which the Nix
build replays all of the evidence.

## Limits

- The probes show one build and one or two plans for each query; they do not show what SQLite
  promises.
- The prototype uses Lean's `List.Perm` and its quotient, and it proves the laws for any type of
  rows. It does not connect to the model's `Value` type or to its evaluator; slice 2 of the ADR
  does that.
- The kernel cost is the cost of one equality of two bags. A model test that enumerates many
  choices decides many such equalities.
