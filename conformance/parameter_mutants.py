"""Mutants of parameters (ADR 0019, slice 1; plans/20261023-parameters.task.md).

The task lists the changes that the conformance suite must notice. Each mutant is one text change
in a copy of the model, which `conformance.resolve_mutants.measure` builds and runs against its
target case of `conformance.authored_parameters`. The two mutants of the numbering (`?` numbered
from the count of earlier parameters, and one number for `:a` and `@a`) change the frontend
(`Translation/Parameters.lean`), which numbers the parameters before the model sees them; the
measurement copies only the model and the conformance runner, so they are not in this table.
"""

from conformance.resolve_mutants import SQLITE

OPERANDS = SQLITE + "Resolution/OperandTraced.lean"
"""The resolution of the operands of an expression, with their affinities."""
TERMS = SQLITE + "Resolution/QueryTerms.lean"
"""The result column that an `ORDER BY` or `GROUP BY` term names."""
WINDOW = SQLITE + "QueryWindow.lean"
"""The integer that SQLite reads from a bound `LIMIT` or `OFFSET` value."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "parameter_affinity": (OPERANDS,
        "  | .parameter number => pure (.parameter number, none)",
        "  | .parameter number => pure (.parameter number, some .numeric)"),
    "order_by_parameter_column": (TERMS,
        "  | .identifier name _ => (aliasIndex names name).map .ok\n"
        "  | term@.null | term@(.numeric _) | term@(.string _) | term@(.blob _) | term@(.parameter _) | term@(.currentTime _)",
        "  | .identifier name _ => (aliasIndex names name).map .ok\n"
        "  | .parameter number => some (if 1 ≤ number ∧ number ≤ names.length then .ok (number - 1) else .error ())\n"
        "  | term@.null | term@(.numeric _) | term@(.string _) | term@(.blob _) | term@(.currentTime _)"),
    "limit_accepts_fraction": (WINDOW,
        "  | .null | .real _ | .text _ | .blob _ => none",
        "  | .real bits => match castValue .integer (.real bits) with\n"
        "    | .integer whole => some whole\n"
        "    | .null | .real _ | .text _ | .blob _ => none\n"
        "  | .null | .text _ | .blob _ => none"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list of the task: a parameter with an affinity (NUMERIC), `ORDER BY ?` as a
column number (the number of the parameter, which the target case binds to the same integer), and
a `LIMIT ?` that accepts a real with a fraction (truncated, as `CAST` does)."""

TARGETS: dict[str, tuple[str, ...]] = {
    "parameter_affinity": ("parameter-no-affinity",),
    "order_by_parameter_column": ("parameter-order-by",),
    "limit_accepts_fraction": ("parameter-limit-refused-fraction",),
}
"""The authored case of `conformance.authored_parameters` that each mutant changes."""

GUARDS: dict[str, str] = {
    "parameter_affinity": "rule:resolveOperandTraced",
    "order_by_parameter_column": "rule:namedResult",
    "limit_accepts_fraction": "rule:windowInteger",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
