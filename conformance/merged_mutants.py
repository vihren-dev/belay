"""Mutants of USING and NATURAL with RIGHT and FULL joins (ADR 0012, amendment 3, slice 4d).

The task of slice 4d lists the changes that the conformance suite must notice. Each
mutant is one text change in a copy of the model, which
`conformance.resolve_mutants.measure` builds and runs against its target case of
`conformance.authored_merged`.
"""

from conformance.resolve_mutants import SQLITE

SCOPE = SQLITE + "Resolution/Scope.lean"
"""The resolution of unqualified names over the sources."""
MERGED_NAMES = SQLITE + "Resolution/MergedNames.lean"
"""The operands of merged names and the expansion of `*`."""
MERGED_LEFT = SQLITE + "Resolution/MergedLeft.lean"
"""The left side of a generated condition."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "right_merged_uses_left": (SCOPE, "      | .takeRight => .found first [source.offset + index]",
        "      | .takeRight => .found first reads"),
    "full_merged_uses_left": (SCOPE, "      | .coalesce => .found first (reads ++ [source.offset + index])",
        "      | .coalesce => .found first reads"),
    "coalesce_keeps_affinity": (MERGED_NAMES, "  | reads => (coalesceColumns reads, none)",
        "  | reads => (coalesceColumns reads,\n"
        "      (reads.head?.bind (scope.columns[·]?)).map CatalogColumn.affinity)"),
    "later_using_left_most": (MERGED_LEFT,
        "  | first :: rest => some (left.nameOperand (if coalesced then first :: rest else [first]))",
        "  | first :: rest => some (left.nameOperand (if false then first :: rest else [first]))"),
    "ambiguous_reference_accepted": (MERGED_LEFT, "  if ((left.namedColumns name).drop 1).all (·.2.2) then .ok name",
        "  if true then .ok name"),
    "star_shows_own_column": (MERGED_NAMES, "  if rightAfter && mergedLater then match scope.resolveName column.name with",
        "  if false then match scope.resolveName column.name with"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list in the task of slice 4d: a right join's merged name
keeps the left column; a full join's merged name keeps the left column instead of the
coalesce; the coalesce keeps the left column's affinity; a later USING compares the
left-most column instead of the coalesce; a left table that does not merge the name is
accepted instead of `ambiguous reference to a in USING()`; `*` and `x.*` show each
table's own column instead of the merged name."""

TARGETS: dict[str, tuple[str, ...]] = {
    "right_merged_uses_left": ("merged-right-column",), "full_merged_uses_left": ("merged-full-coalesce",),
    "coalesce_keeps_affinity": ("merged-full-where-text",), "later_using_left_most": ("merged-right-then-using",),
    "ambiguous_reference_accepted": ("merged-ambiguous-reference",), "star_shows_own_column": ("merged-full-star",),
}
"""The authored case of `conformance.authored_merged` that each mutant changes."""

GUARDS: dict[str, str] = {
    "right_merged_uses_left": "rule:Scope.resolveStep", "full_merged_uses_left": "rule:Scope.resolveStep",
    "coalesce_keeps_affinity": "rule:Scope.nameOperand", "later_using_left_most": "rule:mergedLeft",
    "ambiguous_reference_accepted": "rule:usingReferenceChecked", "star_shows_own_column": "rule:Scope.starOperand",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
