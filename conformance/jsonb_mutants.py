"""Mutants of JSONB (ADR 0015, slice 4).

The task of slice 4 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_jsonb`.
"""

from conformance.resolve_mutants import SQLITE

JSONB = SQLITE + "Json/Jsonb.lean"
"""The JSONB encoder and reader."""
BUILD = SQLITE + "Json/Build.lean"
"""The SQL values that the JSON functions store."""
EXTRACT = SQLITE + "Json/Extract.lean"
"""The JSON argument of a function."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "header_skips_one_size_byte": (JSONB,
        "  else if size ≤ 0xff then [code + 0xc0, size.toUInt8]\n",
        "  else if size ≤ 0 then [code + 0xc0, size.toUInt8]\n"),
    "set_stores_text": (BUILD,
        "      | none => .error .malformed) else .ok (.textraw bytes)\n",
        "      | none => .error .malformed) else .ok (.text bytes)\n"),
    "blob_never_text": (EXTRACT,
        "    | .notJsonb => parseTextArgument bytes\n",
        "    | .notJsonb => .error .malformed\n"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 4: a header whose size needs one byte written
with two, `jsonb_set` that stores SQL text as `TEXT` instead of `TEXTRAW`, and a BLOB that is
never read as JSON text."""

TARGETS: dict[str, tuple[str, ...]] = {
    "header_skips_one_size_byte": ("jsonb-header-sizes",),
    "set_stores_text": ("jsonb-edit",),
    "blob_never_text": ("jsonb-blob-as-text",),
}
"""The authored case of `conformance.authored_jsonb` that each mutant changes."""

GUARDS: dict[str, str] = {
    "header_skips_one_size_byte": "rule:jsonbHeader",
    "set_stores_text": "rule:sqlValueNode",
    "blob_never_text": "rule:parseJsonArgument",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
