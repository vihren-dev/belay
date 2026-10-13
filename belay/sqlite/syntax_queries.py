"""Map a single-table SELECT to statement syntax (ADR 0012, slice 1).

A query keeps its result columns with their source text, which SQLite uses as the
column name, its table, and its WHERE, GROUP BY, ORDER BY, LIMIT and OFFSET
clauses. Inside a query, an expression may also be a comparison, AND, OR, NOT,
IS NULL, arithmetic, unary minus or plus of any expression, CAST with its type
name as written, or a function call with `*` or with one or more arguments, with
the function name as written: Lean folds the name and decides the function. A call
with two or more arguments is a chain of `callPair` nodes. Other statements keep
the expressions of `syntax_expressions.expression`. Compound SELECT, WITH,
DISTINCT, HAVING, joins, `table.*`, NULLS FIRST or LAST and calls without
arguments have no constructor and are refused with their source range.
"""

from .located import Located, constructor, leaf, sequence, structure
from .sql_tree import Node, Tree
from .syntax_definitions import absent, left_list, require
from .syntax_expressions import dequote, expression, name

COMPARISONS = {"NE": "ne", "LT": "lt", "LE": "le", "GT": "gt", "GE": "ge"}
"""Comparison tokens other than `=`, and their `Comparison` constructors in Lean."""
CONNECTIVES = {"AND": "and", "OR": "or"}
"""Logical tokens and their `Syntax.Expr` constructors in Lean."""
ARITHMETIC = {"PLUS": "add", "MINUS": "subtract", "STAR": "multiply", "SLASH": "divide", "REM": "remainder"}
"""Arithmetic tokens and their `ArithmeticOperator` constructors in Lean."""


def binary(tree: Tree, node: Node, kind: str, left: Node, right: Node) -> Located:
    """A constructor with a left and a right operand."""
    return constructor(kind, [("left", query_expression(tree, left)), ("right", query_expression(tree, right))],
                       node.start, node.end)


def compare(tree: Tree, node: Node, operator: str, left: Node, right: Node, kind: str = "compare") -> Located:
    """A comparison other than `=`, or an arithmetic operator: a constructor with an
    operator and two operands."""
    return constructor(kind, [("operator", leaf(operator, node.start, node.end)),
                                   ("left", query_expression(tree, left)),
                                   ("right", query_expression(tree, right))], node.start, node.end)


def is_null(tree: Tree, node: Node, operand: Node, negated: bool) -> Located:
    """`IS NULL`, `ISNULL`, `NOTNULL` or `NOT NULL`."""
    return constructor("isNull", [("operand", query_expression(tree, operand)),
                                  ("negated", leaf(negated, node.start, node.end))], node.start, node.end)


def call_pairs(tree: Tree, start: int, end: int, function: Located, arguments: list[Node]) -> Located:
    """Two or more arguments as a chain of `callPair` nodes over a byte range: the first
    argument, then the rest as another pair from the second argument on, or the last argument."""
    rest = (query_expression(tree, arguments[1]) if len(arguments) == 2
            else call_pairs(tree, arguments[1].start, end, function, arguments[1:]))
    return constructor("callPair", [("name", function), ("first", query_expression(tree, arguments[0])),
                                    ("rest", rest)], start, end)


def function_call(tree: Tree, node: Node, children: list[Node]) -> Located:
    """A call with `*` or with one or more arguments, with the function name as written."""
    function = name(tree, children[0])
    if [child.symbol for child in children] == ["ID", "LP", "STAR", "RP"]:
        return constructor("callStar", [("name", function)], node.start, node.end)
    if [child.symbol for child in children] == ["ID", "LP", "distinct", "exprlist", "RP"]:
        absent(tree, children[2], "DISTINCT in a function call")
        arguments = left_list(tree, children[3], {1: ["nexprlist"]})
        items = left_list(tree, arguments[0][0], {1: ["expr"], 3: ["nexprlist", "COMMA", "expr"]}) if arguments else []
        if len(items) == 1:
            return constructor("call", [("name", function), ("operand", query_expression(tree, items[0][-1]))],
                               node.start, node.end)
        if len(items) > 1:
            return call_pairs(tree, node.start, node.end, function, [item[-1] for item in items])
    raise tree.unsupported(node, "Only COUNT(*), COUNT, MIN and MAX of one argument, and COALESCE are modeled as functions")


def query_expression(tree: Tree, node: Node) -> Located:
    """Map an `expr` production of a query, or refuse it with its range."""
    children = tree.children(node)
    symbols = [child.symbol for child in children]
    if symbols == ["LP", "expr", "RP"]:
        return query_expression(tree, children[1])
    if len(symbols) == 3 and symbols[0] == symbols[2] == "expr":
        if symbols[1] == "EQ":
            return binary(tree, node, "equals", children[0], children[2])
        if symbols[1] in COMPARISONS:
            return compare(tree, node, COMPARISONS[symbols[1]], children[0], children[2])
        if symbols[1] == "IS":
            return compare(tree, node, "is", children[0], children[2])
        if symbols[1] in CONNECTIVES:
            return binary(tree, node, CONNECTIVES[symbols[1]], children[0], children[2])
        if symbols[1] in ARITHMETIC:
            return compare(tree, node, ARITHMETIC[symbols[1]], children[0], children[2], "arithmetic")
    if symbols == ["expr", "IS", "NOT", "expr"]:
        return compare(tree, node, "isNot", children[0], children[3])
    if symbols in (["MINUS", "expr"], ["PLUS", "expr"]):
        kind = "negate" if symbols[0] == "MINUS" else "positive"
        return constructor(kind, [("operand", query_expression(tree, children[1]))], node.start, node.end)
    if symbols == ["CAST", "LP", "expr", "AS", "typetoken", "RP"]:
        return constructor("cast", [("operand", query_expression(tree, children[2])),
                                    ("typeName", leaf(tree.text(children[4]), children[4].start, children[4].end))],
                           node.start, node.end)
    if symbols == ["NOT", "expr"]:
        return constructor("not", [("operand", query_expression(tree, children[1]))], node.start, node.end)
    if symbols in (["expr", "ISNULL"], ["expr", "NOTNULL"], ["expr", "NOT", "NULL"]):
        return is_null(tree, node, children[0], symbols[1] != "ISNULL")
    if symbols[:2] == ["ID", "LP"]:
        return function_call(tree, node, children)
    return expression(tree, node)


def result_column(tree: Tree, node: Node, parts: list[Node]) -> Located:
    """Map `*`, or an expression with its optional alias and its source text."""
    symbols = [part.symbol for part in parts]
    if symbols == ["scanpt", "STAR"]:
        return leaf("star", parts[1].start, parts[1].end)
    if symbols != ["scanpt", "expr", "scanpt", "as"]:
        raise tree.unsupported(node, "Only `*` and expressions are modeled as result columns; write the column names")
    alias_parts = tree.children(parts[3])
    if [part.symbol for part in alias_parts] == ["AS", "nm"]:
        alias = name(tree, alias_parts[1])
    elif alias_parts:
        alias = leaf(dequote(tree.text(alias_parts[0])), parts[3].start, parts[3].end)
    else:
        alias = leaf(None, parts[3].start, parts[3].end)
    value = parts[1]
    return constructor("expression", [("value", query_expression(tree, value)), ("alias", alias),
                                      ("text", leaf(tree.text(value), value.start, value.end))],
                       value.start, max(value.end, parts[3].end))


def result_columns(tree: Tree, node: Node) -> Located:
    """Map the result column list in source order."""
    items: list[Located] = []
    current = node
    while True:
        children = tree.children(current)
        items.append(result_column(tree, current, children[1:]))
        nested = tree.children(children[0])
        if not nested:
            break
        current = require(tree, children[0], ["selcollist", "COMMA"])[0]
    items.reverse()
    return sequence(items, node.start, node.end)


def order_terms(tree: Tree, node: Node) -> list[Located]:
    """Map the ORDER BY terms in source order, with their direction."""
    terms: list[Located] = []
    for item in left_list(tree, node, {3: ["expr", "sortorder", "nulls"],
                                       5: ["sortlist", "COMMA", "expr", "sortorder", "nulls"]}):
        term, direction, nulls = item[-3:]
        absent(tree, nulls, "NULLS FIRST or NULLS LAST")
        descending = [child.symbol for child in tree.children(direction)] == ["DESC"]
        terms.append(structure([("expression", query_expression(tree, term)),
                                ("descending", leaf(descending, direction.start, direction.end))],
                               term.start, max(term.end, direction.end)))
    return terms


def optional(located: Located | None, node: Node) -> Located:
    """An optional part: the located value, or a null leaf at the clause."""
    return located if located is not None else leaf(None, node.start, node.end)


def select(tree: Tree, command: Node) -> Located:
    """Map `SELECT ... FROM table [WHERE] [GROUP BY] [ORDER BY] [LIMIT [OFFSET]]` from one table."""
    (current,) = require(tree, command, ["select"])
    (current,) = require(tree, current, ["selectnowith"])
    (one,) = require(tree, current, ["oneselect"])
    _, distinct, columns, source, where, group, having, order, limit = require(tree, one, [
        "SELECT", "distinct", "selcollist", "from", "where_opt", "groupby_opt", "having_opt", "orderby_opt", "limit_opt"])
    absent(tree, distinct, "DISTINCT or ALL")
    absent(tree, having, "HAVING")
    if not source.children:
        raise tree.unsupported(one, "A SELECT without FROM is not modeled; select from a table")
    _, tables = require(tree, source, ["FROM", "seltablist"])
    prefix, table, schema, alias, join = require(tree, tables, ["stl_prefix", "nm", "dbnm", "as", "on_using"])
    for part, feature in ((prefix, "A join"), (schema, "A schema name"), (alias, "A table alias"),
                          (join, "ON or USING")):
        absent(tree, part, feature)
    condition = query_expression(tree, tree.children(where)[1]) if where.children else None
    grouping = [query_expression(tree, item[-1]) for item in left_list(
        tree, tree.children(group)[2], {1: ["expr"], 3: ["nexprlist", "COMMA", "expr"]})] if group.children else []
    ordering = order_terms(tree, tree.children(order)[2]) if order.children else []
    bounds = tree.children(limit)
    window = [child.symbol for child in bounds]
    count = offset = None
    if window == ["LIMIT", "expr"]:
        count = query_expression(tree, bounds[1])
    elif window in (["LIMIT", "expr", "OFFSET", "expr"], ["LIMIT", "expr", "COMMA", "expr"]):
        first, second = query_expression(tree, bounds[1]), query_expression(tree, bounds[3])
        count, offset = (first, second) if window[2] == "OFFSET" else (second, first)
    elif window:
        raise tree.unsupported(limit, "Unsupported LIMIT form; write LIMIT n [OFFSET m]")
    return constructor("select", [
        ("columns", result_columns(tree, columns)), ("table", name(tree, table)),
        ("filter", optional(condition, where)), ("groupBy", sequence(grouping, group.start, group.end)),
        ("orderBy", sequence(ordering, order.start, order.end)), ("limit", optional(count, limit)),
        ("offset", optional(offset, limit))], command.start, command.end)
