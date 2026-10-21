"""Map the expression forms of a query that hold subqueries or lists (ADR 0018).

`EXISTS (q)`, `x [NOT] IN (q)` and the scalar subquery `(q)` name a subquery of the statement's
list (`syntax_subqueries`, D1); `x [NOT] IN (values)`, `x [NOT] BETWEEN a AND b`, `CASE ... END`
and `x || y` are their own forms (D2). Each function takes the mapper of the operands,
`syntax_queries.query_expression`, which calls them.
"""

from collections.abc import Callable

from .located import Located, constructor, leaf, sequence
from .sql_tree import Node, Tree
from .syntax_shapes import left_list
from .syntax_subqueries import lift

Mapper = Callable[[Tree, Node], Located]
"""The mapper of an operand `expr` production."""


def subquery(tree: Tree, node: Node, children: list[Node], symbols: list[str], expression: Mapper) -> Located | None:
    """`EXISTS (q)`, `x [NOT] IN (q)` and the scalar subquery `(q)`, which name the subquery `q`
    by its index in the statement's list (`syntax_subqueries.lift`); None for another form."""
    if symbols == ["LP", "select", "RP"]:
        return constructor("subquery", [("index", leaf(lift(tree, children[1]), node.start, node.end))],
                           node.start, node.end)
    if symbols == ["EXISTS", "LP", "select", "RP"]:
        return constructor("exists", [("index", leaf(lift(tree, children[2]), node.start, node.end))],
                           node.start, node.end)
    if symbols == ["expr", "in_op", "LP", "select", "RP"]:
        operand = expression(tree, children[0])
        negated = [child.symbol for child in tree.children(children[1])] == ["NOT", "IN"]
        return constructor("inQuery", [("operand", operand),
                                       ("index", leaf(lift(tree, children[3]), node.start, node.end)),
                                       ("negated", leaf(negated, children[1].start, children[1].end))],
                           node.start, node.end)
    return None


def list_form(tree: Tree, node: Node, children: list[Node], symbols: list[str], expression: Mapper) -> Located | None:
    """`x [NOT] IN (values)`, `x [NOT] BETWEEN a AND b`, `CASE ... END` and `x || y` (ADR 0018,
    D2); None for another form. A list of one parenthesized subquery is `x IN (SELECT ...)`, as
    SQLite's parser reads it."""
    if symbols == ["expr", "in_op", "LP", "exprlist", "RP"]:
        negated = leaf([c.symbol for c in tree.children(children[1])] == ["NOT", "IN"], children[1].start,
                       children[1].end)
        listed = left_list(tree, children[3], {1: ["nexprlist"]})
        items = left_list(tree, listed[0][0], {1: ["expr"], 3: ["nexprlist", "COMMA", "expr"]}) if listed else []
        values = [item[-1] for item in items]
        single = [child.symbol for child in tree.children(values[0])] if len(values) == 1 else []
        if single == ["LP", "select", "RP"]:
            index = lift(tree, tree.children(values[0])[1])
            return constructor("inQuery", [("operand", expression(tree, children[0])),
                                           ("index", leaf(index, node.start, node.end)), ("negated", negated)],
                               node.start, node.end)
        mapped = [expression(tree, value) for value in values]
        return constructor("inList", [("operand", expression(tree, children[0])),
                                      ("values", sequence(mapped, children[3].start, children[3].end)),
                                      ("negated", negated)], node.start, node.end)
    if symbols == ["expr", "between_op", "expr", "AND", "expr"]:
        negated = [c.symbol for c in tree.children(children[1])] == ["NOT", "BETWEEN"]
        return constructor("between", [("operand", expression(tree, children[0])),
                                       ("low", expression(tree, children[2])),
                                       ("high", expression(tree, children[4])),
                                       ("negated", leaf(negated, children[1].start, children[1].end))],
                           node.start, node.end)
    if symbols == ["CASE", "case_operand", "case_exprlist", "case_else", "END"]:
        base = tree.children(children[1])
        arms = [part for item in left_list(tree, children[2], {4: ["WHEN", "expr", "THEN", "expr"],
                                                                5: ["case_exprlist", "WHEN", "expr", "THEN", "expr"]})
                for part in (item[-3], item[-1])]
        otherwise = tree.children(children[3])
        operands = [expression(tree, part) for part in base + arms + otherwise[1:]]
        return constructor("caseOf", [("operands", sequence(operands, children[1].start, children[3].end)),
                                      ("hasBase", leaf(bool(base), children[1].start, children[1].end))],
                           node.start, node.end)
    if symbols == ["expr", "CONCAT", "expr"]:
        return constructor("concatenate", [("left", expression(tree, children[0])),
                                           ("right", expression(tree, children[2]))], node.start, node.end)
    return None
