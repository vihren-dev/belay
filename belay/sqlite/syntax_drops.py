"""Map DROP TABLE and DROP INDEX to statement syntax (ADR 0014, slice 7).

Each statement names one object and may have `IF EXISTS`. Resolution decides what the name
refers to, so the frontend keeps the name as written; a schema name stays a refusal, as for
the other statements.
"""

from .located import Located, constructor, leaf
from .sql_tree import Node, Tree
from .syntax_expressions import name
from .syntax_shapes import require


def drop(tree: Tree, command: Node) -> Located:
    """Map `DROP TABLE [IF EXISTS] name` to `dropTable` and `DROP INDEX [IF EXISTS] name` to
    `dropIndex`, with `ifExists` true when the statement has `IF EXISTS`."""
    parts = tree.children(command)
    kind = parts[1].symbol if len(parts) > 1 else ""
    _, _, exists, full = require(tree, command, ["DROP", kind, "ifexists", "fullname"])
    names = tree.children(full)
    if [child.symbol for child in names] != ["nm"]:
        raise tree.unsupported(full, "A schema name is not modeled; remove it")
    constructor_name = "dropTable" if kind == "TABLE" else "dropIndex"
    return constructor(constructor_name, [("name", name(tree, names[0])),
                                          ("ifExists", leaf(bool(exists.children), exists.start, exists.end))],
                       command.start, command.end)
