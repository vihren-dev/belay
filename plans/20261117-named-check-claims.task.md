# Prove a SQL claim given by its name

Created 2026-11-17. Issue [#358](https://github.com/vihren-dev/belay/issues/358).
Status: open.

For the query claim selectClaim in SelectCheckCases.lean, the named and
expanded forms of #sql_check must both report a proof. The printed proof
must elaborate against the original name, including when another definition
names the first claim. A named false claim must still give a replayable
counterexample. The proof must pass the same dependency audit as the
expanded claim.

The default search opens the goal before it chooses a program or query
route. A user definition can hide the binders that the opening introduces.
Expansion must retain the program or query structure that the tactic reads.
The checker must stay within its existing budget.

## Acceptance

Exercise the named and expanded query, a name for the named query, and a
named false claim through #sql_check. Recheck the emitted proof against the
name. Keep the budget tests in tests/surface_search_test.py and the cancellation
and excluded-rule cases in tests/surface_select_procedure_test.py.
