"""Check the shape of parser productions and flatten SQLite's left-recursive lists.

The frontend modules use these helpers to read a production with exactly the symbols
that they map, and to refuse every other form with its source range and the forms that
the model describes.
"""

from .sql_tree import Node, Tree

MODELED_FORMS = ("rewrite it with the modeled forms: CREATE TABLE, CREATE [UNIQUE] INDEX, ALTER TABLE ADD COLUMN, "
                 "BEGIN, COMMIT, ROLLBACK, INSERT ... VALUES, UPDATE ... SET ... [WHERE column = value] and "
                 "SELECT ... FROM table [WHERE] [GROUP BY] [ORDER BY] [LIMIT]")
"""The corrective action for a production that has no syntax constructor."""


def require(tree: Tree, node: Node, symbols: list[str]) -> list[Node]:
    """Return the children of a production with exactly these symbols, or refuse it."""
    children = tree.children(node)
    if [child.symbol for child in children] != symbols:
        raise tree.unsupported(node, f"Unsupported SQL form: {node.symbol}; {MODELED_FORMS}")
    return children


def absent(tree: Tree, node: Node, feature: str) -> None:
    """Refuse optional syntax that is present."""
    if node.children:
        raise tree.unsupported(node, f"{feature} is not modeled; remove it")


def left_list(tree: Tree, node: Node, shapes: dict[int, list[str]]) -> list[list[Node]]:
    """Flatten a left-recursive list in source order; an empty list node ends the list.

    `shapes` maps the child count of a list node to its symbols. Each item is the
    children of one list node after the nested list node.
    """
    items: list[list[Node]] = []
    while node.children:
        children = tree.children(node)
        expected = shapes.get(len(children))
        if expected is None or [child.symbol for child in children] != expected:
            raise tree.unsupported(node, f"Unsupported SQL form: {node.symbol}; {MODELED_FORMS}")
        if children[0].symbol != node.symbol:
            items.append(children)
            break
        items.append(children[1:])
        node = children[0]
    return list(reversed(items))
