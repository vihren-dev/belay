"""Mutants of conflict algorithms (ADR 0012, amendment 4, slice 5d).

The task of slice 5d lists the changes that the conformance suite must notice. Each
mutant is one text change in a copy of the model, which
`conformance.resolve_mutants.measure` builds and runs against its target case of
`conformance.authored_algorithms`.
"""

from conformance.resolve_mutants import SQLITE

RUN = SQLITE + "UpsertRun.lean"
"""The rows of an INSERT with conflict algorithms."""
EXECUTION = SQLITE + "SqlExecution.lean"
"""The SQL step, which rolls back a transaction."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "fail_keeps_no_row": (RUN, "  | .constraintFail => database.set at_ reached", "  | .constraintFail => database"),
    "ignore_stops": (RUN, "  | .ignore => .ok (table, none)", "  | .ignore => .error (failureError .abort)"),
    "replace_first_key_only": (RUN,
        "  { table with rows := table.rows.filter fun row => !((List.range keys.length).any fun index =>",
        "  { table with rows := table.rows.filter fun row => !((List.range 1).any fun index =>"),
    "replace_blocks": (RUN, "    algorithmAt algorithms index != .replace && conflictsAt keys table proposed index",
        "    conflictsAt keys table proposed index"),
    "rollback_keeps_transaction": (EXECUTION, "  if reason = .constraintRollback then match state.snapshot with",
        "  if false then match state.snapshot with"),
    "not_null_ignores_algorithm": (RUN,
        "  | some column => failedConstraint table (algorithmAt policy.notNull column)",
        "  | some _ => failedConstraint table .abort"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list in the task of slice 5d: FAIL keeps no row;
IGNORE stops at the row; REPLACE deletes only the rows of the first key, so a row that
conflicts on two keys keeps one; a REPLACE key fails as ABORT; ROLLBACK keeps the
transaction open; a NOT NULL failure ignores its algorithm."""

TARGETS: dict[str, tuple[str, ...]] = {
    "fail_keeps_no_row": ("or-fail",), "ignore_stops": ("or-ignore",),
    "replace_first_key_only": ("or-replace-two-rows",), "replace_blocks": ("replace-into",),
    "rollback_keeps_transaction": ("or-rollback-transaction",), "not_null_ignores_algorithm": ("or-ignore-not-null",),
}
"""The authored case of `conformance.authored_algorithms` that each mutant changes."""

GUARDS: dict[str, str] = {
    "fail_keeps_no_row": "rule:failedDatabase", "ignore_stops": "rule:failedConstraint",
    "replace_first_key_only": "rule:replaced", "replace_blocks": "rule:blockingKey",
    "rollback_keeps_transaction": "rule:SqlState.failed", "not_null_ignores_algorithm": "rule:upsertRow",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
