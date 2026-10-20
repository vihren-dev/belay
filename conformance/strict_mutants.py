"""Mutants of `STRICT` tables (ADR 0014, slice 6).

The task of slice 6 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_strict`.
"""

from conformance.resolve_mutants import SQLITE

STRICT_TYPES = SQLITE + "Resolution/StrictTypes.lean"
"""Which values each strict type stores."""
CATALOG = SQLITE + "Resolution/Catalog.lean"
"""The affinity of a catalog column."""
UPSERT_RUN = SQLITE + "UpsertRun.lean"
"""The checks of one row of an INSERT with an `OR` algorithm or clauses."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "strict_null_fails": (STRICT_TYPES, "  | _, .null => true", "  | _, .null => false"),
    "any_has_affinity": (CATALOG,
        "  if column.strictType == some .any then .blob else affinityOf column.declaredType",
        "  affinityOf column.declaredType"),
    "ignore_skips_type_error": (UPSERT_RUN,
        "  | none => if !typesFit table.shape proposed then failedConstraint table .abort else",
        "  | none => if !typesFit table.shape proposed then failedConstraint table policy.check else"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 6: a type check that NULL fails, `ANY` with
the affinity of its declared type, and an `OR IGNORE` that skips a row with a type error."""

TARGETS: dict[str, tuple[str, ...]] = {
    "strict_null_fails": ("strict-nulls",),
    "any_has_affinity": ("strict-coercion",),
    "ignore_skips_type_error": ("strict-or-ignore",),
}
"""The authored case of `conformance.authored_strict` that each mutant changes."""

GUARDS: dict[str, str] = {
    "strict_null_fails": "rule:StrictType.fits",
    "any_has_affinity": "rule:CatalogColumn.affinity",
    "ignore_skips_type_error": "rule:upsertRow",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
