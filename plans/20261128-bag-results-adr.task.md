# Experiments and ADR: query results as bags

Created 2026-11-28. DONE on 2026-11-28: the ADR is PROPOSED and waits for the owner.
Status: [20261128-bag-results-adr.status.md](20261128-bag-results-adr.status.md).
Discussion: [Belay issue 489](https://github.com/vihren-dev/belay/issues/489), comment of
2026-11-28 ("Rethinking `A ~ B`").

A query without ORDER BY gives rows in an order that SQLite does not promise. The model gives
these rows as a list in a normal form (`Resolved.normalForm`). ORDER BY with ties gives each tie
group in normal form, and the output (`Output.rows`) joins the groups into one list. Thus the
output does not record which order SQLite promises. LIMIT and OFFSET without a total order can give
two or more different results; the output is then a choice (`Output.oneOf`), a list of lists.
When every choice gives the same rows, the output is `Output.rows`.

The owner proposed on 2026-11-28 that the result of a query without ORDER BY is a bag (a
multiset), that ORDER BY can make a list of it, and that LIMIT of a bag is a bag that is not
determined: any sub-bag of the limit's size. When fewer rows remain after OFFSET, the size is
the number of the remaining rows. (SQLite treats a negative LIMIT as no limit and a negative
OFFSET as 0.) A bag is then known by its rows, or as the result of
a nondeterministic program whose inputs are bags.

This task runs experiments on this idea and writes an ADR for its implementation. The owner
expects two parts: a separate Lean module with all facts about bags, and then the integration of
this module into the rest of the code, which replaces lists with bags in many places.

## What is true when the task is done

1. **Prototype of the bag module.** `experiments/bag-results/` holds a Lean prototype that uses
   only the Lean core library and no model code. It defines nondeterministic results, bags,
   ranked results (tie groups in order), the choices that LIMIT, OFFSET and DISTINCT make, ORDER
   BY, and the equivalence of two results by the lists that an application can read. It proves,
   with no `sorry`:
   - the algebra of bags that reduction needs: filter, map, UNION ALL and product;
   - the description of LIMIT as a sub-bag of the rows that remain after OFFSET, and that its
     row count is determined: for a negative limit, which SQLite treats as no limit, the count is
     the number of remaining rows; otherwise it is the smaller of the limit and that number;
   - that the ranked result of ORDER BY (its tie groups in order) does not depend on the order
     of its input, when the sort keys are total functions of the row, as in the prototype; and
     that a reader that is a function of the bag of rows cannot see an ORDER BY without LIMIT.
     In SQLite a sort key can fail, for example with an integer overflow, and then ORDER BY
     changes the result from rows to an error. The ADR says how the model treats such errors
     and which SQLite readers are functions of the bag. Other readers can see the order: a
     scalar subquery reads its first row, as LIMIT 1 does, and in the probes an outer
     `group_concat` over a FROM subquery reads the order of the subquery. In a join, native
     SQLite can ignore the ORDER BY of a FROM subquery;
   - that OFFSET and LIMIT over ranked rows take a slice of each list that the rows permit,
     with a negative OFFSET as 0 and a negative LIMIT as no limit;
   - a canonical form of ranked rows: two ranked results permit the same lists exactly when
     their canonical forms are equal;
   - that for two nondeterministic results whose every value is one tie group (a bag),
     equivalence is equality of the sets of permitted bags;
   - for a type with a total, transitive and antisymmetric order, a sample of each bag (its
     rows sorted, owner request of 2026-11-28): two bags are equal exactly when their samples
     are equal.
2. **Current behavior.** An experiment shows, with the pinned model package, that the model gives
   equal outputs for a query without ORDER BY and for queries with ORDER BY, and shows with native
   SQLite that an application reads different lists from them.
3. **Cost of the representation.** An experiment measures the kernel cost of deciding the
   equality of two bags of rows in two representations: a quotient of lists and the normal-form
   list of the model. For the quotient, it measures two decisions: by `List.Perm`, and by the
   equality of the samples of the two bags (owner request of 2026-11-28).
4. **SQLite behavior for the semantic decisions.** Native SQLite probes, with their recorded
   results, show what SQLite does for: LIMIT without ORDER BY, ties of ORDER BY, the row that
   DISTINCT keeps under a collation, the order of `group_concat`, the order of a sum of REAL
   values, a CTE with LIMIT that a query reads two times, a correlated subquery with LIMIT, and
   ORDER BY in a subquery. The probes show what one pinned build does for one plan or for a few
   plans; they do not show what SQLite promises.
5. **Integration survey.** A record lists the code that depends on list-valued outputs: the model,
   the surface package, the codec, the conformance harness, the judge and its corpora, tests and
   documentation, with counts.
6. **Findings.** `experiments/bag-results/README.md` gives the results and how to reproduce them.
7. **ADR.** `docs/adr/adr-0034-bag-results.md` (status PROPOSED) decides the bag module, its
   place and its interface, the integration and its slices, what each slice shows, and lists the
   owner decisions.

## Test suite

- `nix-build experiments/bag-results/default.nix` builds every Lean file of the experiment
  against the pinned toolchain and model package. It fails when a file has `sorry`, and it
  records the axioms of each main theorem: only `propext`, `Classical.choice` and `Quot.sound`
  are allowed.
- The native probes run from one script with the pinned SQLite, and their output is recorded
  next to the script.

## Points to know

- Many tests of the model decide outputs with `decide +kernel`, for example
  `Schema/Dispatch/PossibleResultsExamples.lean`. Equality of two bags as a quotient is
  decidable with `Quotient.decidableEq` and the decision of `List.Perm`, and `decide +kernel`
  must reduce that procedure in the kernel.
- Ranked results with equal rows in separate groups permit the same lists, for example
  `[{a}, {a}]` and `[{a, a}]`. A comparison by data needs the canonical form.
- OFFSET and LIMIT can cut one tie group on both sides.
- The model already enumerates the choices of LIMIT and OFFSET
  (`Queries/Evaluation/PossibleResults.lean`, `Output.ofResults`).
- A change of the output encoding can change the codec, the conformance harness and the judge.
  A change of the judge or of a corpus needs its own pull request with the owner's approval
  (ADR 0011).
- The [simplification goal](../docs/development/lean-simplification-goal.md) limits maintained
  Lean lines and fixes a capability baseline. New code under `experiments/` counts as
  maintained code, so the README records the code lines of the prototype, and the ADR counts
  them in its line estimate. The prototype changes no capability of the baseline. The ADR
  estimates the net line change of the integration and states its effects on the capability
  baseline separately.
- A local result is not evidence. The findings cite the Nix build of the experiment.
