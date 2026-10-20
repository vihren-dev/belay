"""Mutants of CHECK constraints (ADR 0014, slice 4).

The task of slice 4 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_checks`.
"""

from conformance.resolve_mutants import SQLITE

LITERAL_DATA = SQLITE + "LiteralData.lean"
"""The CHECK of a row and the constraints of a stored table."""
UPSERT_RUN = SQLITE + "UpsertRun.lean"
"""The rows of an INSERT with clauses or conflict algorithms."""

CHECK_STEP = ("    if !checksHold table.shape proposed then failedConstraint table policy.check else\n"
              "    match handlingClause keys clauses table proposed with")
"""The CHECK step of `upsertRow`, after NOT NULL and the types of a `STRICT` table, and before
the unique keys."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "check_null_fails": (LITERAL_DATA, "  value.isNull || Resolved.truthy value", "  Resolved.truthy value"),
    "check_after_keys": (UPSERT_RUN, CHECK_STEP, "    match handlingClause keys clauses table proposed with"),
    "check_replace_skips": (UPSERT_RUN, CHECK_STEP,
        CHECK_STEP.replace("failedConstraint table policy.check",
                           "failedConstraint table (if policy.check == .replace then .ignore else policy.check)")),
    "check_skipped": (LITERAL_DATA, "  table.rows.all (checksHold table.shape) &&\n", ""),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 4: a CHECK that NULL fails, CHECK after the
unique keys, REPLACE that skips the row for a CHECK, and a write that skips the CHECK."""

TARGETS: dict[str, tuple[str, ...]] = {
    "check_null_fails": ("check-null-passes",),
    "check_after_keys": ("check-before-unique",),
    "check_replace_skips": ("check-or-replace",),
    "check_skipped": ("check-update",),
}
"""The authored case of `conformance.authored_checks` that each mutant changes."""

GUARDS: dict[str, str] = {
    "check_null_fails": "rule:checkHolds",
    "check_after_keys": "rule:upsertRow",
    "check_replace_skips": "rule:upsertRow",
    "check_skipped": "rule:constraints",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
