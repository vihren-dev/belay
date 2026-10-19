"""Map CHECK, CONSTRAINT names and foreign keys of CREATE TABLE (ADR 0014, slice 4).

SQLite's parser keeps the name of the last `CONSTRAINT name` in effect: within a column
definition until the next column, and from the last column into the table constraints
until a comma between two table constraints. Only a CHECK reports the name. The frontend
gives each CHECK the label that SQLite reports when it fails: the name in effect, else the
source text between the parentheses without outer white space, dequoted when it starts
with a quote. Foreign keys keep only their column lists: with foreign keys off, SQLite
checks only their number.
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


def references(tree: Tree, node: Node, parts: list[Node]) -> Located:
    """Map a column's `REFERENCES table [(columns)]`, dropping its clauses."""
    return constructor("references", [("table", name(tree, parts[1])), ("columns", optional_names(tree, parts[2]))],
                       node.start, node.end)


def foreign_key(tree: Tree, node: Node, parts: list[Node]) -> Located:
    """Map `FOREIGN KEY (columns) REFERENCES table [(columns)]`, dropping its clauses."""
    return constructor("foreignKey", [("columns", plain_names(tree, parts[3])), ("table", name(tree, parts[6])),
                                      ("referenced", optional_names(tree, parts[7]))], node.start, node.end)
