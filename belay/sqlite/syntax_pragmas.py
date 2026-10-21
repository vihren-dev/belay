"""Map `PRAGMA foreign_keys` to statement syntax (ADR 0018, D4).

`PRAGMA foreign_keys` reads the setting and `PRAGMA foreign_keys = value` or
`PRAGMA foreign_keys(value)` sets it. A value is one of the words that SQLite's
`sqlite3GetBoolean` reads, `on`, `off`, `yes`, `no`, `true` and `false` in either ASCII case,
also quoted, or the integer 0 or 1. Every other pragma, a schema name and another value are
refused with their source range.
"""

from .located import Located, constructor, leaf
from .sql_tree import Node, Tree
from .syntax_constraints import ascii_equal
from .syntax_expressions import dequote

WORDS = {"on": True, "yes": True, "true": True, "off": False, "no": False, "false": False}
"""The boolean words of `sqlite3GetBoolean`, which it compares with ASCII case ignored."""


def setting_value(tree: Tree, node: Node) -> bool:
    """The boolean of an `nmnum` value, or a refusal for a value outside `WORDS`, 0 and 1."""
    parts = tree.children(node)
    symbols = [part.symbol for part in parts]
    if symbols == ["plus_num"] and [child.symbol for child in tree.children(parts[0])] == ["INTEGER"]:
        number = tree.text(parts[0])
        if number in ("0", "1"):
            return number == "1"
    elif symbols in (["ON"], ["nm"]):
        word = dequote(tree.text(parts[0])) if symbols == ["nm"] else "on"
        for known, value in WORDS.items():
            if ascii_equal(word, known):
                return value
    raise tree.unsupported(node, "Only on, off, yes, no, true, false, 0 and 1 are modeled as the value of "
                           "PRAGMA foreign_keys")


def pragma(tree: Tree, command: Node) -> Located:
    """Map `PRAGMA foreign_keys [= value]` and `PRAGMA foreign_keys(value)` to
    `pragmaForeignKeys`, whose `value` is none for the query form."""
    parts = tree.children(command)
    symbols = [part.symbol for part in parts]
    if len(parts) < 3 or not ascii_equal(dequote(tree.text(parts[1])), "foreign_keys") or parts[2].children:
        raise tree.unsupported(command, "Only PRAGMA foreign_keys is modeled, without a schema name")
    if symbols == ["PRAGMA", "nm", "dbnm"]:
        value: bool | None = None
    elif symbols in (["PRAGMA", "nm", "dbnm", "EQ", "nmnum"], ["PRAGMA", "nm", "dbnm", "LP", "nmnum", "RP"]):
        value = setting_value(tree, parts[4])
    else:
        raise tree.unsupported(command, "Only on, off, yes, no, true, false, 0 and 1 are modeled as the value of "
                               "PRAGMA foreign_keys")
    return constructor("pragmaForeignKeys", [("value", leaf(value, command.start, command.end))],
                       command.start, command.end)
