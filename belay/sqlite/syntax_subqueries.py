"""Lift the subqueries of a statement into its list (ADR 0018, D1).

An expression names a subquery by its index in the list, in the order of the subqueries'
text, and each subquery names the query around it: `None` for the statement's query or
write, else the index of an earlier subquery. `syntax_select.select` and the writes of
`syntax_writes` open the list for a statement; outside it, such as in a CHECK constraint, and
in RETURNING and ON CONFLICT, a subquery has no constructor and is refused with its source
range.
"""

from collections.abc import Callable, Iterator
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field

from .located import Json, Located, leaf, sequence, structure
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
"""The list of the statement whose expressions the frontend maps, if any."""

OUTSIDE = "A subquery is modeled only in SELECT, INSERT VALUES, UPDATE and DELETE; rewrite the statement without it"
"""The refusal of a subquery outside a statement that lists subqueries, such as in a CHECK constraint."""

REFUSAL: ContextVar[str] = ContextVar("subquery_refusal", default=OUTSIDE)
"""The refusal of a subquery where no list is open."""


@contextmanager
def statement_subqueries(clauses: Clauses) -> Iterator[SubqueryList]:
    """Open the list of subqueries of one statement while its expressions are mapped."""
    token = ACTIVE.set(SubqueryList(clauses))
    try:
        listed = ACTIVE.get()
        assert listed is not None
        yield listed
    finally:
        ACTIVE.reset(token)


@contextmanager
def no_subqueries(refusal: str) -> Iterator[None]:
    """Refuse every subquery, with the refusal, while a clause whose subqueries the model does
    not place is mapped, such as RETURNING."""
    active, message = ACTIVE.set(None), REFUSAL.set(refusal)
    try:
        yield
    finally:
        REFUSAL.reset(message)
        ACTIVE.reset(active)


def lift(tree: Tree, select: Node) -> int:
    """Add the subquery of a `select` production to the statement's list and return its index;
    its own subqueries come after it. Refuse it where no list is open."""
    listed = ACTIVE.get()
    if listed is None:
        raise tree.unsupported(select, REFUSAL.get())
    index = len(listed.items)
    listed.items.append(None)
    around, listed.current = listed.current, index
    try:
        clauses = listed.clauses(tree, select)
    finally:
        listed.current = around
    listed.items[index] = structure(clauses[:8] + [("parent", leaf(around, select.start, select.end))] + clauses[8:],
                                    select.start, select.end)
    return index


DEFAULTS: dict[str, Json] = {"subqueries": [], "having": None, "distinct": False}
"""The fields that a statement's JSON omits when they have these values, so that statements
without them keep the form that frozen records hold; Lean reads a missing field as its default."""


def with_subqueries(name: str, fields: list[tuple[str, Located]], listed: SubqueryList, start: int, end: int,
                    after: list[tuple[str, Located]] | None = None) -> Located:
    """The statement constructor with its fields, the `subqueries` field and the fields `after`
    it, in the order of the Lean constructor, so a path of a Lean issue selects the right part.
    The JSON omits each field of `DEFAULTS` that has its default value."""
    items = [item for item in listed.items if item is not None]
    parts = fields + [("subqueries", sequence(items, start, end))] + (after or [])
    value = {field: part.value for field, part in parts if not (field in DEFAULTS and part.value == DEFAULTS[field])}
    return Located({name: value}, start, end, tuple(part for _, part in parts))
