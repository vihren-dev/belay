"""Map the FROM clause of a SELECT to its first table and its joins (ADR 0012, amendment 2).

A table reference is a table name with an optional alias. Each join after the first
table has the keywords of its operator as written, its table, and its optional ON
condition and USING column names. Lean reads the kind of the join from the keywords
and decides which joins the model describes, so this module does not fold their case. Schema names, INDEXED BY, table-valued functions and subqueries in FROM have
no constructor and are refused with their source range.
"""

from collections.abc import Callable

from .located import Located, constructor, leaf, sequence, structure
from .sql_tree import Node, Tree
from .syntax_definitions import absent, left_list, require
from .syntax_expressions import dequote, name

def alias(tree: Tree, node: Node) -> Located:
    """The alias of an `as` node: `AS name`, a bare name, or none."""
    parts = tree.children(node)
    if [part.symbol for part in parts] == ["AS", "nm"]:
        return name(tree, parts[1])
    if parts:
        return leaf(dequote(tree.text(parts[0])), node.start, node.end)
    return leaf(None, node.start, node.end)


def table_reference(tree: Tree, table: Node, schema: Node, alias_node: Node) -> Located:
    """A table name with its optional alias; a schema name is refused."""
    absent(tree, schema, "A schema name")
    return structure([("table", name(tree, table)), ("alias", alias(tree, alias_node))],
                     table.start, max(table.end, alias_node.end))


def join_operator(tree: Tree, node: Node) -> Located:
    """The keywords of a `joinop` before `JOIN`, as written; none for `,` and a plain `JOIN`."""
    words = [leaf(tree.text(part), part.start, part.end) for part in tree.children(node)
             if part.symbol not in ("COMMA", "JOIN")]
    return sequence(words, node.start, node.end)


def join_constraint(tree: Tree, node: Node, condition: Callable[[Tree, Node], Located]) -> tuple[Located, Located]:
    """The ON condition and the USING column names of an `on_using` node, each a null
    leaf when absent."""
    parts = tree.children(node)
    symbols = [part.symbol for part in parts]
    missing = leaf(None, node.start, node.end)
    if symbols == ["ON", "expr"]:
        return condition(tree, parts[1]), missing
    if symbols == ["USING", "LP", "idlist", "RP"]:
        names = [name(tree, item[-1]) for item in left_list(tree, parts[2], {1: ["nm"], 3: ["idlist", "COMMA", "nm"]})]
        return missing, sequence(names, parts[2].start, parts[2].end)
    return missing, missing


def from_clause(tree: Tree, tables: Node,
                condition: Callable[[Tree, Node], Located]) -> tuple[Located, Located]:
    """The first table of a `seltablist` and its joins in order; `condition` maps an ON
    expression. A table-valued function or a subquery is refused."""
    items: list[tuple[Node, list[Node]]] = []
    current = tables
    while True:
        parts = tree.children(current)
        if [part.symbol for part in parts] != ["stl_prefix", "nm", "dbnm", "as", "on_using"]:
            raise tree.unsupported(current, "Only tables, with optional aliases, are modeled in FROM; "
                                   "write table names and joins")
        items.append((current, parts))
        prefix = tree.children(parts[0])
        if not prefix:
            break
        current = require(tree, parts[0], ["seltablist", "joinop"])[0]
    items.reverse()
    first_node, (_, table, schema, alias_node, constraint) = items[0]
    absent(tree, constraint, "ON or USING on the first table")
    first = table_reference(tree, table, schema, alias_node)
    joins: list[Located] = []
    for index, (node, (prefix, table, schema, alias_node, constraint)) in enumerate(items[1:], start=1):
        operator = require(tree, prefix, ["seltablist", "joinop"])[1]
        on, using = join_constraint(tree, constraint, condition)
        joins.append(structure([
            ("operator", join_operator(tree, operator)), ("source", table_reference(tree, table, schema, alias_node)),
            ("condition", on),
            ("usingColumns", using)], operator.start, node.end))
    return first, sequence(joins, first_node.end, tables.end)
