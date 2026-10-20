"""Lift the subqueries of a SELECT into the statement's list (ADR 0018, D1).

An expression names a subquery by its index in the list, in the order of the subqueries'
text, and each subquery names the query around it: `None` for the statement's query, else
the index of an earlier subquery. `syntax_select.select` opens the list for a statement;
outside it, such as in a CHECK constraint or a write, a subquery has no constructor and is
refused with its source range.
"""

from collections.abc import Callable, Iterator
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field

from .located import Located, leaf, sequence, structure
from .sql_tree import Node, Tree

Clauses = Callable[[Tree, Node], list[tuple[str, Located]]]
"""Map a `select` production to the clauses of `Syntax.Subquery` without its parent."""


@dataclass
class SubqueryList:
    """The subqueries of one statement so far, and the index of the query being mapped."""

    clauses: Clauses
    items: list[Located | None] = field(default_factory=list)
    current: int | None = None


ACTIVE: ContextVar[SubqueryList | None] = ContextVar("subqueries", default=None)
"""The list of the statement whose SELECT the frontend maps, if any."""


@contextmanager
def statement_subqueries(clauses: Clauses) -> Iterator[SubqueryList]:
    """Open the list of subqueries of one statement while its SELECT is mapped."""
    token = ACTIVE.set(SubqueryList(clauses))
    try:
        listed = ACTIVE.get()
        assert listed is not None
        yield listed
    finally:
        ACTIVE.reset(token)


def lift(tree: Tree, select: Node) -> int:
    """Add the subquery of a `select` production to the statement's list and return its index;
    its own subqueries come after it. Refuse it outside a SELECT statement."""
    listed = ACTIVE.get()
    if listed is None:
        raise tree.unsupported(select, "A subquery is modeled only in a SELECT statement; rewrite the statement without it")
    index = len(listed.items)
    listed.items.append(None)
    around, listed.current = listed.current, index
    try:
        clauses = listed.clauses(tree, select)
    finally:
        listed.current = around
    listed.items[index] = structure(clauses + [("parent", leaf(around, select.start, select.end))],
                                    select.start, select.end)
    return index


def subquery_list(listed: SubqueryList, start: int, end: int) -> Located:
    """The located list of the statement's subqueries."""
    items = [item for item in listed.items if item is not None]
    return sequence(items, start, end)
