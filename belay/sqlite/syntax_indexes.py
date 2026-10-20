"""Map CREATE [UNIQUE] INDEX to statement syntax (ADR 0014, slice 1).

An index has key terms, each an expression with an optional sort order, and an optional
`WHERE` filter. Resolution decides which terms and filters the model describes, so the
frontend maps every expression form that a query may use.
"""

from .located import Located, constructor, leaf, sequence
from .sql_tree import Node, Tree
from .syntax_shapes import absent, require
from .syntax_expressions import name
from .syntax_queries import query_expression
from .syntax_select import order_terms


def create_index(tree: Tree, command: Node) -> Located:
    """Map CREATE [UNIQUE] INDEX name ON table(terms) [WHERE filter]."""
    parts = require(tree, command, ["createkw", "uniqueflag", "INDEX", "ifnotexists", "nm", "dbnm", "ON", "nm",
                                    "LP", "sortlist", "RP", "where_opt"])
    absent(tree, parts[3], "IF NOT EXISTS")
    absent(tree, parts[5], "A schema name")
    where = tree.children(parts[11])
    filter_ = query_expression(tree, where[1]) if where else leaf(None, parts[11].start, parts[11].end)
    return constructor("createIndex", [("name", name(tree, parts[4])),
                                       ("unique", leaf(bool(parts[1].children), parts[1].start, parts[1].end)),
                                       ("table", name(tree, parts[7])),
                                       ("terms", sequence(order_terms(tree, parts[9]), parts[9].start, parts[9].end)),
                                       ("filter", filter_)], command.start, command.end)
