"""Mutants of derived-source scope, column metadata and membership certainty (ADR 0019, D5)."""

from conformance.resolve_mutants import SQLITE

MUTANTS: dict[str, tuple[str, str, str]] = {
    "cte_outer_scope_ignored": (SQLITE + "Resolution/CommonTableScope.lean",
        "        | some query => findCommonTable queries name fuel query.parent\n",
        "        | some query => none\n"),
    "cte_recursion_not_registered": (SQLITE + "Resolution/CommonTableExpansion.lean",
        "            recursive := state.recursive ++ [(index, copiedTerms.map Prod.snd)] }\n",
        "            recursive := state.recursive }\n"),
    "source_sibling_binding": (SQLITE + "Resolution/SubqueryScopes.lean",
        "  let derived := around.sourceIndexes.contains index\n",
        "  let derived := false\n"),
    "source_affinity_lost": (SQLITE + "Resolution/DerivedColumns.lean",
        "    affinities := some (columns.map (·.affinity)),\n",
        "    affinities := some (columns.map (fun _ => none)),\n"),
    "source_collation_lost": (SQLITE + "Resolution/DerivedColumns.lean",
        "      { name := Identifier.ofString column.name, declaredType := column.declaredType, collation := column.collation },\n",
        "      { name := Identifier.ofString column.name, declaredType := column.declaredType, collation := .binary },\n"),
    "source_uncertainty_ignored": (SQLITE + "Subqueries.lean",
        "        sourceCertain := bound.windowCertain context source.rows bound.limit true,\n",
        "        sourceCertain := true,\n"),
}
"""One exact change per mutant; each measurement builds only its changed classifier closure."""

TARGETS: dict[str, tuple[str, ...]] = {
    "cte_outer_scope_ignored": ("cte-forward",),
    "cte_recursion_not_registered": ("cte-recursive",),
    "source_sibling_binding": ("source-sibling-refused",),
    "source_affinity_lost": ("source-all-metadata",),
    "source_collation_lost": ("source-all-metadata",),
    "source_uncertainty_ignored": ("source-limit-second-column-uncertain",),
}
"""Native source cases that distinguish each changed rule from the original model."""

GUARDS: dict[str, str] = {
    "cte_outer_scope_ignored": "rule:findCommonTable",
    "cte_recursion_not_registered": "rule:copyCommonTableQuery",
    "source_sibling_binding": "rule:subqueryScope",
    "source_affinity_lost": "rule:derivedScopeSource",
    "source_collation_lost": "rule:derivedScopeSource",
    "source_uncertainty_ignored": "rule:Query.subqueryRun",
}
"""The model declarations whose meaning each mutant checks."""
