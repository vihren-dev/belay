"""Mutants of index forms (ADR 0014, slice 1).

The task of slice 1 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_indexes`.
"""

from conformance.resolve_mutants import SQLITE

LITERAL_DATA = SQLITE + "LiteralData.lean"
"""The key equality of the execution semantics."""
EXECUTION = SQLITE + "Execution.lean"
"""The execution of CREATE INDEX."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "index_filter_ignored": (LITERAL_DATA, "  | some filter => Resolved.truthy (filter.eval 0 row.values)",
        "  | some filter => true"),
    "index_expression_as_column": (LITERAL_DATA, "  | .expression value => some (value.eval 0 row.values)",
        "  | .expression value => read row 0"),
    "index_built_without_check": (EXECUTION,
        "        if index.unique && !LiteralData.uniqueRows index.uniqueKey table.rows then",
        "        if false then"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 1: a filter that is ignored, an expression
key read as the first column, and a CREATE INDEX that runs without its uniqueness check."""

TARGETS: dict[str, tuple[str, ...]] = {
    "index_filter_ignored": ("index-partial-outside",),
    "index_expression_as_column": ("index-expression-conflict",),
    "index_built_without_check": ("index-runs-unique-duplicates",),
}
"""The authored case of `conformance.authored_indexes` that each mutant changes."""

GUARDS: dict[str, str] = {
    "index_filter_ignored": "rule:keyApplies", "index_expression_as_column": "rule:termValue",
    "index_built_without_check": "rule:step",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
