"""Map CREATE TRIGGER and DROP TRIGGER to statement syntax (ADR 0018, D5).

A trigger keeps its name, `IF NOT EXISTS`, its time (`BEFORE`, also without a time, or
`AFTER`), its event (`INSERT`, `UPDATE [OF columns]` or `DELETE`), its table, its `WHEN`
condition and the statements of its body in order. A body statement is an INSERT with
VALUES rows, an UPDATE, a DELETE or a SELECT, each with the fields of its Lean
`Syntax.BodyStatement` constructor and the subqueries of its expressions; a body has no
RETURNING. `TEMP`, `INSTEAD OF`, a schema name, a qualified table name, `INDEXED BY`,
`UPDATE OR`, `UPDATE FROM`, WITH, RETURNING and a subquery in `WHEN` have no constructor and
are refused with their source range.
"""

from .located import Located, constructor, leaf, sequence
from .sql_tree import Node, Tree
from .syntax_conflicts import assignment_list, conflict_clauses, insert_algorithm
from .syntax_expressions import name
from .syntax_queries import query_expression
from .syntax_select import query_clauses
from .syntax_shapes import absent, left_list, require
from .syntax_subqueries import SubqueryList, no_subqueries, statement_subqueries
from .syntax_writes import value_rows

IN_WHEN = "A subquery in the WHEN condition of a trigger is not modeled; move the test into the trigger's statements"
"""The refusal of a subquery in `WHEN`."""


def body_statement(kind: str, fields: list[tuple[str, Located]], listed: SubqueryList, node: Node,
                   after: list[tuple[str, Located]] | None = None) -> Located:
    """The body statement constructor with every field, the `subqueries` field included, in
    the order of the Lean constructor; unlike a statement, a body statement omits no field."""
    items = [item for item in listed.items if item is not None]
    parts = fields + [("subqueries", sequence(items, node.start, node.end))] + (after or [])
    return constructor(kind, parts, node.start, node.end)


def body_table(tree: Tree, node: Node) -> Located:
    """The table of a body statement, a `trnm` node; a qualified name is refused, as SQLite
    refuses it inside a trigger."""
    parts = tree.children(node)
    if [part.symbol for part in parts] != ["nm"]:
        raise tree.unsupported(node, "A qualified table name is not allowed in a trigger; write the table name")
    return name(tree, parts[0])


def body_filter(tree: Tree, where: Node) -> Located:
    """The optional WHERE filter of a `where_opt` node, a null leaf without it."""
    parts = tree.children(where)
    return query_expression(tree, parts[1]) if parts else leaf(None, where.start, where.end)


def body_insert(tree: Tree, node: Node) -> Located:
    """`INSERT [OR algorithm] INTO table [(columns)] VALUES rows [ON CONFLICT ...]` and
    `REPLACE INTO` in a trigger body."""
    _, operation, _, target, columns, source, upsert, _ = require(
        tree, node, ["scanpt", "insert_cmd", "INTO", "trnm", "idlist_opt", "select", "upsert", "scanpt"])
    with no_subqueries("A subquery in ON CONFLICT is not modeled; read the value in a separate statement"):
        conflicts, returned = conflict_clauses(tree, upsert)
    if returned:
        raise tree.unsupported(upsert, "RETURNING is not allowed in a trigger; remove it")
    if columns.children:
        _, listed_names, _ = require(tree, columns, ["LP", "idlist", "RP"])
        names = [name(tree, item[-1]) for item in left_list(tree, listed_names, {1: ["nm"], 3: ["idlist", "COMMA", "nm"]})]
        column_list = sequence(names, columns.start, columns.end)
    else:
        column_list = leaf(None, columns.start, columns.end)
    with statement_subqueries(query_clauses) as listed:
        rows = value_rows(tree, source)
    return body_statement("insert", [("table", body_table(tree, target)), ("columns", column_list), ("rows", rows),
                                     ("conflicts", conflicts), ("algorithm", insert_algorithm(tree, operation))],
                          listed, node)


def body_update(tree: Tree, node: Node) -> Located:
    """`UPDATE table SET assignments [WHERE expression]` in a trigger body."""
    _, conflict, target, indexed, _, assignments, from_, where, _ = require(
        tree, node, ["UPDATE", "orconf", "trnm", "tridxby", "SET", "setlist", "from", "where_opt", "scanpt"])
    absent(tree, conflict, "An OR conflict clause of UPDATE")
    absent(tree, indexed, "INDEXED BY")
    absent(tree, from_, "UPDATE FROM")
    with statement_subqueries(query_clauses) as listed:
        mapped, filter_ = assignment_list(tree, assignments), body_filter(tree, where)
    return body_statement("update", [("table", body_table(tree, target)), ("assignments", mapped),
                                     ("filter", filter_)], listed, node)


def body_delete(tree: Tree, node: Node) -> Located:
    """`DELETE FROM table [WHERE expression]` in a trigger body."""
    _, _, target, indexed, where, _ = require(tree, node, ["DELETE", "FROM", "trnm", "tridxby", "where_opt", "scanpt"])
    absent(tree, indexed, "INDEXED BY")
    with statement_subqueries(query_clauses) as listed:
        filter_ = body_filter(tree, where)
    return body_statement("delete", [("table", body_table(tree, target)), ("filter", filter_)], listed, node)


def body_select(tree: Tree, node: Node) -> Located:
    """A SELECT in a trigger body, with every clause of `Syntax.BodyStatement.select`."""
    _, select_node, _ = require(tree, node, ["scanpt", "select", "scanpt"])
    with statement_subqueries(query_clauses) as listed:
        clauses = query_clauses(tree, select_node)
    return body_statement("select", clauses[:8], listed, node, clauses[8:])


BODY = {"UPDATE": body_update, "DELETE": body_delete}
"""The body statements whose `trigger_cmd` starts with their keyword."""


def body(tree: Tree, node: Node) -> Located:
    """The statements of a `trigger_cmd_list` node in source order."""
    items: list[Located] = []
    for item in left_list(tree, node, {2: ["trigger_cmd", "SEMI"], 3: ["trigger_cmd_list", "trigger_cmd", "SEMI"]}):
        command = item[-2]
        symbols = [child.symbol for child in tree.children(command)]
        if symbols[:1] in (["UPDATE"], ["DELETE"]):
            items.append(BODY[symbols[0]](tree, command))
        elif symbols[1:2] == ["insert_cmd"]:
            items.append(body_insert(tree, command))
        else:
            items.append(body_select(tree, command))
    return sequence(items, node.start, node.end)


def trigger_time(tree: Tree, node: Node) -> Located:
    """`before` for BEFORE and for a trigger without a time, `after` for AFTER; INSTEAD OF,
    which needs a view, is refused."""
    symbols = [child.symbol for child in tree.children(node)]
    if symbols == ["INSTEAD", "OF"]:
        raise tree.unsupported(node, "INSTEAD OF triggers are not modeled, as the model has no views; "
                               "write the statements on the tables instead")
    return leaf("after" if symbols == ["AFTER"] else "before", node.start, node.end)


def trigger_event(tree: Tree, node: Node) -> Located:
    """`insert`, `delete`, or `update` with the column names of `UPDATE OF`, empty without OF."""
    parts = tree.children(node)
    symbols = [part.symbol for part in parts]
    if symbols in (["INSERT"], ["DELETE"]):
        return leaf({"INSERT": "insert", "DELETE": "delete"}[symbols[0]], node.start, node.end)
    columns = [name(tree, item[-1]) for item in left_list(tree, parts[2], {1: ["nm"], 3: ["idlist", "COMMA", "nm"]})] \
        if symbols == ["UPDATE", "OF", "idlist"] else []
    return constructor("update", [("columns", sequence(columns, node.start, node.end))], node.start, node.end)


def create_trigger(tree: Tree, command: Node) -> Located:
    """Map `CREATE TRIGGER [IF NOT EXISTS] name [BEFORE|AFTER] event ON table [FOR EACH ROW]
    [WHEN condition] BEGIN statements END` to `createTrigger`."""
    _, declaration, _, statements, _ = require(tree, command, ["createkw", "trigger_decl", "BEGIN", "trigger_cmd_list", "END"])
    temp, _, exists, trigger_name, schema, time, event, _, table, _, when = require(tree, declaration, [
        "temp", "TRIGGER", "ifnotexists", "nm", "dbnm", "trigger_time", "trigger_event", "ON", "fullname",
        "foreach_clause", "when_clause"])
    absent(tree, temp, "A TEMP trigger")
    absent(tree, schema, "A schema name")
    names = tree.children(table)
    if [child.symbol for child in names] != ["nm"]:
        raise tree.unsupported(table, "A schema name is not modeled; remove it")
    with no_subqueries(IN_WHEN):
        condition = query_expression(tree, tree.children(when)[1]) if when.children else leaf(None, when.start, when.end)
    return constructor("createTrigger", [
        ("name", name(tree, trigger_name)), ("ifNotExists", leaf(bool(exists.children), exists.start, exists.end)),
        ("time", trigger_time(tree, time)), ("event", trigger_event(tree, event)), ("table", name(tree, names[0])),
        ("condition", condition), ("body", body(tree, statements))], command.start, command.end)
