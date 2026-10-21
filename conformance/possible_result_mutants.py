"""Mutants of the results that SQLite may give (ADR 0018, slice 6).

The task of slice 6 lists the changes that the conformance suite must notice. Each mutant is
one text change in a copy of the model, which `conformance.resolve_mutants.measure` builds and
runs against its target case of `conformance.authored_possible_results`.
"""

from conformance.resolve_mutants import SQLITE

RESULTS = SQLITE + "PossibleResults.lean"
"""The list of the results that SQLite may give."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "ignores_offset": (RESULTS,
        "  distinctLists (choiceResults (windowChoices query.offset query.stop 0 (query.tieGroupRows context rows)))",
        "  distinctLists (choiceResults (windowChoices 0 query.stop 0 (query.tieGroupRows context rows)))"),
    "only_first_choice": (RESULTS,
        "  else distinctLists ((choose (groupSlice start stop position group).length group).map normalForm)",
        "  else [normalForm (groupSlice start stop position group)]"),
    "one_row_too_many": (RESULTS,
        "  else distinctLists ((choose (groupSlice start stop position group).length group).map normalForm)",
        "  else distinctLists ((choose ((groupSlice start stop position group).length + 1) group).map normalForm)"),
    "desc_not_reversed": (RESULTS,
        "  stableSort (fun a b => (compareSort (query.orderBy.map fun term => (term.descending, term.collation)) a.2 b.2).isLE)",
        "  stableSort (fun a b => (compareSort (query.orderBy.map fun term => (false, term.collation)) a.2 b.2).isLE)"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 6: a list that ignores `OFFSET`, a list with only
the choice of `Query.results`, a list that cuts a group with one row too many, and groups that
`DESC` does not reverse."""

TARGETS: dict[str, tuple[str, ...]] = {
    "ignores_offset": ("ties-offset",),
    "only_first_choice": ("index-order",),
    "one_row_too_many": ("ties-limit",),
    "desc_not_reversed": ("ties-desc",),
}
"""The authored case of `conformance.authored_possible_results` that each mutant changes."""

GUARDS: dict[str, str] = {
    "ignores_offset": "rule:Query.possibleResults",
    "only_first_choice": "rule:groupChoices",
    "one_row_too_many": "rule:groupChoices",
    "desc_not_reversed": "rule:Query.sortedRecords",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
