"""Map CHECK, CONSTRAINT names and foreign keys of CREATE TABLE (ADR 0014, slice 4).

SQLite's parser keeps the name of the last `CONSTRAINT name` in effect: within a column
definition until the next column, and from the last column into the table constraints
until a comma between two table constraints. Only a CHECK reports the name. The frontend
gives each CHECK the label that SQLite reports when it fails: the name in effect, else the
source text between the parentheses without outer white space, dequoted when it starts
with a quote. Foreign keys keep their column lists and their `ON DELETE` and `ON UPDATE`
actions, which `PRAGMA foreign_key_list` reports; a later clause of an action replaces an
earlier one, and `MATCH`, `ON INSERT` and a deferral clause do not show.
"""

from .located import Located, constructor, leaf, sequence
from .sql_tree import Node, Tree
from .syntax_expressions import dequote, name
from .syntax_queries import query_expression
from .syntax_shapes import absent, left_list, require

SPACE = " \t\n\f\r\v"
"""The bytes that `sqlite3Isspace` accepts, which SQLite trims from a CHECK label."""


def constraint_name(tree: Tree, node: Node) -> str:
    """The name of a `CONSTRAINT name` production as SQLite reports it: dequoted."""
    return dequote(tree.text(node))


def check(tree: Tree, node: Node, parts: list[Node], current: str | None) -> Located:
    """Map `CHECK (expr)` with its label: the name in effect, else the text between the
    parentheses, trimmed and dequoted."""
    left, condition, right = parts[1], parts[2], parts[3]
    text = tree.sql[left.end:right.start].decode("utf-8").strip(SPACE)
    label = current if current is not None else dequote(text)
    return constructor("check", [("condition", query_expression(tree, condition)),
                                 ("label", leaf(label, condition.start, condition.end))], node.start, node.end)


def plain_names(tree: Tree, node: Node) -> Located:
    """Map an `eidlist` of plain names, without collation or sort order."""
    names: list[Located] = []
    for item in left_list(tree, node, {3: ["nm", "collate", "sortorder"],
                                       5: ["eidlist", "COMMA", "nm", "collate", "sortorder"]}):
        column, collation, order = item[-3:]
        absent(tree, collation, "A collation in a foreign key")
        absent(tree, order, "A sort order in a foreign key")
        names.append(name(tree, column))
    return sequence(names, node.start, node.end)


def optional_names(tree: Tree, node: Node) -> Located:
    """Map an `eidlist_opt`: the names of `(names)`, or no names."""
    if not node.children:
        return sequence([], node.start, node.end)
    _, listed, _ = require(tree, node, ["LP", "eidlist", "RP"])
    return plain_names(tree, listed)


ACTIONS = {("SET", "NULL"): "setNull", ("SET", "DEFAULT"): "setDefault", ("CASCADE",): "cascade",
           ("RESTRICT",): "restrict", ("NO", "ACTION"): "noAction"}
"""The `refact` productions and the Lean constructors of `ForeignKeyAction`."""


def actions(tree: Tree, node: Node) -> tuple[Located, Located]:
    """The `ON DELETE` and `ON UPDATE` actions of a `refargs` node, `noAction` without a
    clause; a later clause replaces an earlier one, and `MATCH` and `ON INSERT` are dropped."""
    found = {"DELETE": leaf("noAction", node.start, node.end), "UPDATE": leaf("noAction", node.start, node.end)}
    for item in left_list(tree, node, {2: ["refargs", "refarg"]}):
        parts = tree.children(item[-1])
        symbols = [part.symbol for part in parts]
        if symbols in (["ON", "DELETE", "refact"], ["ON", "UPDATE", "refact"]):
            action = tuple(part.symbol for part in tree.children(parts[2]))
            found[symbols[1]] = leaf(ACTIONS[action], parts[2].start, parts[2].end)
    return found["DELETE"], found["UPDATE"]


def generated(tree: Tree, node: Node, kind: Node) -> Located:
    """Map `AS (expr) [kind]` (ADR 0014, slice 5) with the kind token as written, quotes
    included, or none; resolution decides `VIRTUAL`, `STORED` or SQLite's
    `error in generated column`, which a quoted word also is."""
    parts = tree.children(kind)
    if [part.symbol for part in parts][:3] != ["LP", "expr", "RP"] or len(parts) > 4:
        raise tree.unsupported(kind, "Unsupported generated column; write AS (expression) VIRTUAL or STORED")
    word = leaf(tree.text(parts[3]), parts[3].start, parts[3].end) if len(parts) == 4 else leaf(None, kind.end, kind.end)
    return constructor("generated", [("expression", query_expression(tree, parts[1])), ("kind", word)],
                       node.start, node.end)


def references(tree: Tree, node: Node, parts: list[Node]) -> Located:
    """Map a column's `REFERENCES table [(columns)]` with its actions."""
    on_delete, on_update = actions(tree, parts[3])
    return constructor("references", [("table", name(tree, parts[1])), ("columns", optional_names(tree, parts[2])),
                                      ("onDelete", on_delete), ("onUpdate", on_update)], node.start, node.end)


def foreign_key(tree: Tree, node: Node, parts: list[Node]) -> Located:
    """Map `FOREIGN KEY (columns) REFERENCES table [(columns)]` with its actions."""
    on_delete, on_update = actions(tree, parts[8])
    return constructor("foreignKey", [("columns", plain_names(tree, parts[3])), ("table", name(tree, parts[6])),
                                      ("referenced", optional_names(tree, parts[7])), ("onDelete", on_delete),
                                      ("onUpdate", on_update)], node.start, node.end)
