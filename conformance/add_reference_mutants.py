"""Mutants of the refusal to add a REFERENCES column with a non-NULL default.

Each mutant is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target cases of `conformance.authored_add_references`.
"""

from conformance.resolve_mutants import SQLITE

EXECUTION = SQLITE + "Execution.lean"
"""The step of ADD COLUMN, which refuses a populated table."""
ADD_COLUMN = SQLITE + "Resolution/AddColumn.lean"
"""The resolver of ADD COLUMN, which decides when the statement refuses a populated table."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "add_reference_not_refused": (EXECUTION,
        "      if refusesPopulated && !table.rows.isEmpty then .error (.referenceColumnDefault, database)\n",
        "      if false && !table.rows.isEmpty then .error (.referenceColumnDefault, database)\n"),
    "add_reference_empty_refused": (EXECUTION,
        "      if refusesPopulated && !table.rows.isEmpty then .error (.referenceColumnDefault, database)\n",
        "      if refusesPopulated then .error (.referenceColumnDefault, database)\n"),
    "add_reference_unenforced_refused": (ADD_COLUMN,
        "(enforced && !column.foreignKeys.isEmpty && !literalNullDefault definition)",
        "(!column.foreignKeys.isEmpty && !literalNullDefault definition)"),
    "add_reference_null_refused": (ADD_COLUMN,
        "  | none | some .null => true\n",
        "  | none => true\n  | some .null => false\n"),
    "add_reference_first_default": (ADD_COLUMN,
        "  let written : Option Syntax.Expr := definition.constraints.reverse.findSome?",
        "  let written : Option Syntax.Expr := definition.constraints.findSome?"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement. They
are: a refusal that never happens, a refusal on an empty table, a refusal while foreign keys are
not enforced, a refusal of the NULL default, and a first DEFAULT that decides instead of the last."""

TARGETS: dict[str, tuple[str, ...]] = {
    "add_reference_not_refused": ("add-reference-refused",),
    "add_reference_empty_refused": ("add-reference-empty",),
    "add_reference_unenforced_refused": ("add-reference-unenforced",),
    "add_reference_null_refused": ("add-reference-null",),
    "add_reference_first_default": ("add-reference-last-default",),
}
"""The authored cases of `conformance.authored_add_references` that each mutant changes."""

GUARDS: dict[str, str] = {
    "add_reference_not_refused": "rule:step",
    "add_reference_empty_refused": "rule:step",
    "add_reference_unenforced_refused": "rule:resolveAddColumn",
    "add_reference_null_refused": "rule:literalNullDefault",
    "add_reference_first_default": "rule:literalNullDefault",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
