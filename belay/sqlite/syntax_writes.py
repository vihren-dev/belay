"""Map transaction control, INSERT and UPDATE to statement syntax.

INSERT keeps its optional column list and its VALUES rows; UPDATE keeps its
assignments and its optional WHERE expression. Conflict clauses, RETURNING,
UPSERT, FROM, SELECT sources and named or non-deferred transactions have no
constructor and are refused with their source range.
"""

from .located import Located, constructor, leaf, pair, sequence
from .sql_tree import Node, Tree
from .syntax_definitions import absent, left_list, require
from .syntax_expressions import expression, name


def transaction(tree: Tree, command: Node) -> Located:
    """Map BEGIN [DEFERRED] [TRANSACTION], COMMIT or END [TRANSACTION], and ROLLBACK [TRANSACTION]."""
    children = tree.children(command)
    keyword = children[0].symbol
    if keyword == "BEGIN":
        _, mode, option = require(tree, command, ["BEGIN", "transtype", "trans_opt"])
        if [child.symbol for child in tree.children(mode)] not in ([], ["DEFERRED"]):
            raise tree.unsupported(mode, "Only deferred transactions are modeled; write BEGIN or BEGIN DEFERRED")
    else:
        _, option = require(tree, command, [keyword, "trans_opt"])
    if [child.symbol for child in tree.children(option)] not in ([], ["TRANSACTION"]):
        raise tree.unsupported(option, "Named transactions are not modeled; remove the transaction name")
    kind = {"BEGIN": "begin", "COMMIT": "commit", "END": "commit", "ROLLBACK": "rollback"}[keyword]
    return leaf(kind, command.start, command.end)


def value_rows(tree: Tree, node: Node) -> Located:
    """Map the VALUES rows of an INSERT source, in source order; a SELECT source is refused."""
    current = node
    for symbol in ("selectnowith", "oneselect"):
        (current,) = require(tree, current, [symbol])
    children = tree.children(current)
    if [child.symbol for child in children] not in (["values"], ["mvalues"]):
        raise tree.unsupported(current, "Only VALUES rows are modeled as an INSERT source; "
                               "write INSERT ... VALUES (...)")
    current, listed = children[0], []
    while current.symbol == "mvalues":
        earlier = tree.children(current)[0].symbol if current.children else ""
        parts = require(tree, current, [earlier, "COMMA", "LP", "nexprlist", "RP"])
        listed.append(parts[3])
        current = parts[0]
    listed.append(require(tree, current, ["VALUES", "LP", "nexprlist", "RP"])[2])
    rows = [sequence([expression(tree, item[-1]) for item in
                      left_list(tree, row, {1: ["expr"], 3: ["nexprlist", "COMMA", "expr"]})], row.start, row.end)
            for row in reversed(listed)]
    return sequence(rows, node.start, node.end)


def insert(tree: Tree, command: Node) -> Located:
    """Map INSERT INTO table [(columns)] VALUES rows."""
    with_, operation, _, target, columns, source, upsert = require(
        tree, command, ["with", "insert_cmd", "INTO", "xfullname", "idlist_opt", "select", "upsert"])
    absent(tree, with_, "A WITH clause")
    _, conflict = require(tree, operation, ["INSERT", "orconf"])
    absent(tree, conflict, "An OR conflict clause")
    absent(tree, upsert, "An UPSERT or RETURNING clause")
    (table,) = require(tree, target, ["nm"])
    if columns.children:
        _, listed, _ = require(tree, columns, ["LP", "idlist", "RP"])
        names = [name(tree, item[-1]) for item in left_list(tree, listed, {1: ["nm"], 3: ["idlist", "COMMA", "nm"]})]
        column_list = sequence(names, columns.start, columns.end)
    else:
        column_list = leaf(None, columns.start, columns.end)
    return constructor("insert", [("table", name(tree, table)), ("columns", column_list),
                                  ("rows", value_rows(tree, source))], command.start, command.end)


def update(tree: Tree, command: Node) -> Located:
    """Map UPDATE table SET assignments [WHERE expression]."""
    with_, _, conflict, target, indexed, _, assignments, from_, where = require(
        tree, command, ["with", "UPDATE", "orconf", "xfullname", "indexed_opt", "SET", "setlist", "from",
                        "where_opt_ret"])
    absent(tree, with_, "A WITH clause")
    absent(tree, conflict, "An OR conflict clause")
    absent(tree, indexed, "INDEXED BY")
    absent(tree, from_, "UPDATE FROM")
    (table,) = require(tree, target, ["nm"])
    items = [pair(name(tree, item[-3]), expression(tree, item[-1]), item[-3].start, item[-1].end)
             for item in left_list(tree, assignments, {3: ["nm", "EQ", "expr"],
                                                       5: ["setlist", "COMMA", "nm", "EQ", "expr"]})]
    if where.children:
        _, predicate = require(tree, where, ["WHERE", "expr"])
        filter_ = expression(tree, predicate)
    else:
        filter_ = leaf(None, where.start, where.end)
    return constructor("update", [("table", name(tree, table)),
                                  ("assignments", sequence(items, assignments.start, assignments.end)),
                                  ("filter", filter_)], command.start, command.end)
