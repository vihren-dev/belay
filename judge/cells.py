"""Typed SQLite cells in the recorded transport form, checked without conversion.

Both sides of a comparison use this one form: `"null"`, `{"integer": {"value": n}}`,
`{"real": {"bits": "decimal IEEE bits"}}`, `{"text": {"bytes": [...]}}` and
`{"blob": {"bytes": [...]}}`. Equal cells have equal JSON.
"""

from typing import TypeAlias

Json: TypeAlias = None | bool | int | float | str | list["Json"] | dict[str, "Json"]
"""A decoded JSON value."""

INTEGER_RANGE = range(-(2**63), 2**63)
"""SQLite's 64-bit signed integer range."""


def checked_cell(value: Json) -> Json:
    """Return the cell unchanged if it has a valid transport form; refuse anything else."""
    if value == "null":
        return value
    if isinstance(value, dict) and len(value) == 1:
        kind, payload = next(iter(value.items()))
        if isinstance(payload, dict) and len(payload) == 1:
            if kind == "integer" and type(payload.get("value")) is int and payload["value"] in INTEGER_RANGE:
                return value
            bits = payload.get("bits")
            if kind == "real" and isinstance(bits, str) and bits.isdigit() and int(bits) < 2**64:
                return value
            data = payload.get("bytes")
            if kind in ("text", "blob") and isinstance(data, list) and all(
                    type(byte) is int and 0 <= byte < 256 for byte in data):
                return value
    raise ValueError(f"invalid cell: {value!r}")


def text(value: Json) -> str:
    """The UTF-8 text of a TEXT cell; metadata such as names and types are TEXT cells."""
    checked_cell(value)
    if not isinstance(value, dict) or "text" not in value:
        raise ValueError(f"expected a TEXT cell: {value!r}")
    return bytes(value["text"]["bytes"]).decode("utf-8")


def integer(value: Json) -> int:
    """The value of an INTEGER cell; metadata numbers and row ids are INTEGER cells."""
    checked_cell(value)
    if not isinstance(value, dict) or "integer" not in value:
        raise ValueError(f"expected an INTEGER cell: {value!r}")
    return value["integer"]["value"]
