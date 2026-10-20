"""Mutants of the JSON build and edit functions (ADR 0015, slice 3).

The task of slice 3 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_json_edits`.
"""

from conformance.resolve_mutants import SQLITE

EDIT = SQLITE + "Json/Edit.lean"
"""The edits at a path."""
BUILD = SQLITE + "Json/Build.lean"
"""The functions that build or edit JSON text."""
PATCH = SQLITE + "Json/PatchPretty.lean"
"""The merge patch, the pretty text and the error position."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "insert_overwrites": (EDIT,
        "      | .insert => .edited node\n",
        "      | .insert => .edited value\n"),
    "patch_keeps_null": (PATCH,
        "      | some index, .null => members.eraseIdx index\n",
        "      | some index, .null => members.set index ((members.getD index (.null, .null)).1, .null)\n"),
    "array_quotes_json": (BUILD,
        "  | .text bytes => .ok (if json then bytes else quoted (escapeSqlText bytes))\n",
        "  | .text bytes => .ok (if json && false then bytes else quoted (escapeSqlText bytes))\n"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 3: `json_insert` that overwrites an existing
node, `json_patch` that keeps a member whose patch is `null`, and `json_array` that quotes a
JSON argument."""

TARGETS: dict[str, tuple[str, ...]] = {
    "insert_overwrites": ("json-edit-insert-replace",),
    "patch_keeps_null": ("json-edit-patch",),
    "array_quotes_json": ("json-build-subtype",),
}
"""The authored case of `conformance.authored_json_edits` that each mutant changes."""

GUARDS: dict[str, str] = {
    "insert_overwrites": "rule:editStep",
    "patch_keeps_null": "rule:mergeMembers",
    "array_quotes_json": "rule:sqlValueText",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
