"""Typed records of the facts that the Lean fact reader writes for one module.

The reader (`extractor/LeanCodeStore/Facts.lean`) writes JSON; this module checks its shape at
the boundary so that the folding rules work on typed values only.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import cast

Range = tuple[int, int, int, int, int, int]
"""`(line, column, utf16Column, endLine, endColumn, endUtf16Column)`; lines count from 1."""

Reference = tuple[str, str]
"""A referenced constant as `(name, declaring module)`."""


@dataclass(frozen=True)
class ConstantFacts:
    """The facts of one compiled constant that the rules of "Generated constants" read."""

    name: str
    module: str
    kernel_kind: str
    range: Range | None
    selection: Range | None
    table_parent: str | None
    is_structure: bool
    is_class: bool
    is_instance: bool
    instance_class: str | None
    parents: tuple[Reference, ...]
    is_matcher: bool
    is_reserved: bool
    lean_auto_decl: bool
    type_references: tuple[Reference, ...]
    body_references: tuple[Reference, ...]


@dataclass(frozen=True)
class ModuleFacts:
    """The constants of one module and the facts of the constants that it refers to."""

    module: str
    imports: tuple[str, ...]
    constants: tuple[ConstantFacts, ...]
    external: dict[str, ConstantFacts]
    deriving_commands: dict[str, Range]
    """The range of the `deriving instance` command of each instance that such a command declares."""


def _range(value: object, context: str) -> Range | None:
    """Read an optional six-number range."""
    if value is None:
        return None
    if not isinstance(value, list) or len(value) != 6 or not all(isinstance(x, int) for x in value):
        raise ValueError(f"{context}: a range must be six integers")
    return cast(Range, tuple(value))


def _command_ranges(value: object, context: str) -> dict[str, Range]:
    """Read the `[line, column, endLine, endColumn]` command range of each instance name.

    The UTF-16 columns are not given; the code point columns take their place.
    """
    if not isinstance(value, dict):
        raise ValueError(f"{context}: derivingCommands must be an object")
    ranges: dict[str, Range] = {}
    for name, item in cast(dict[str, object], value).items():
        if not (isinstance(item, list) and len(item) == 4 and all(isinstance(x, int) for x in item)):
            raise ValueError(f"{context}: the command range of {name} must be four integers")
        line, column, end_line, end_column = cast(list[int], item)
        ranges[name] = (line, column, column, end_line, end_column, end_column)
    return ranges


def _references(value: object, context: str) -> tuple[Reference, ...]:
    """Read a list of `[name, module]` pairs."""
    if not isinstance(value, list):
        raise ValueError(f"{context}: references must be a list")
    pairs: list[Reference] = []
    for item in value:
        if not (isinstance(item, list) and len(item) == 2 and all(isinstance(x, str) for x in item)):
            raise ValueError(f"{context}: a reference must be [name, module]")
        pairs.append((item[0], item[1]))
    return tuple(pairs)


def _optional_text(value: object, context: str) -> str | None:
    """Read an optional string."""
    if value is not None and not isinstance(value, str):
        raise ValueError(f"{context}: expected a string or null")
    return value


def _flag(row: dict[str, object], key: str, context: str) -> bool:
    """Read one boolean field."""
    value = row.get(key)
    if not isinstance(value, bool):
        raise ValueError(f"{context}: field {key} must be a boolean")
    return value


def _text(row: dict[str, object], key: str, context: str) -> str:
    """Read one string field."""
    value = row.get(key)
    if not isinstance(value, str):
        raise ValueError(f"{context}: field {key} must be a string")
    return value


def constant_facts(row: object, context: str) -> ConstantFacts:
    """Check and convert one constant record of the fact reader."""
    if not isinstance(row, dict):
        raise ValueError(f"{context}: a constant record must be an object")
    data = cast(dict[str, object], row)
    name = _text(data, "name", context)
    where = f"{context}: {name}"
    return ConstantFacts(
        name=name, module=_text(data, "module", where), kernel_kind=_text(data, "kernelKind", where),
        range=_range(data.get("range"), where), selection=_range(data.get("selection"), where),
        table_parent=_optional_text(data.get("tableParent"), where),
        is_structure=_flag(data, "structure", where), is_class=_flag(data, "class", where),
        is_instance=_flag(data, "instance", where),
        instance_class=_optional_text(data.get("instanceClass"), where),
        parents=_references(data.get("parents", []), where),
        is_matcher=_flag(data, "matcher", where), is_reserved=_flag(data, "reserved", where),
        lean_auto_decl=_flag(data, "leanAutoDecl", where),
        type_references=_references(data.get("type", []), where),
        body_references=_references(data.get("body", []), where))


def module_facts(document: object, context: str) -> ModuleFacts:
    """Check and convert the JSON document of one module."""
    if not isinstance(document, dict):
        raise ValueError(f"{context}: the module document must be an object")
    data = cast(dict[str, object], document)
    imports = data.get("imports")
    constants = data.get("constants")
    external = data.get("external")
    if not isinstance(imports, list) or not all(isinstance(x, str) for x in imports):
        raise ValueError(f"{context}: imports must be a list of module names")
    if not isinstance(constants, list) or not isinstance(external, list):
        raise ValueError(f"{context}: constants and external must be lists")
    external_facts = [constant_facts(row, context) for row in external]
    return ModuleFacts(
        module=_text(data, "module", context), imports=tuple(sorted(set(imports))),
        constants=tuple(constant_facts(row, context) for row in constants),
        external={facts.name: facts for facts in external_facts},
        deriving_commands=_command_ranges(data.get("derivingCommands"), context))
