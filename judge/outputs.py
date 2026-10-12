"""Compare a predicted statement output with the recorded one, including ORDER BY tie groups.

Without tie groups, the rows are compared as a bag. With tie groups, the groups keep
their recorded order and the rows inside one group may come in any order; the first
and last group may be cut by a window (LIMIT). This is the rule of ADR 0005 that
`VerifierConformance/Outputs.lean` applied before the judge existed.
"""

from judge.cells import Json, checked_cell


def rows_of(value: Json) -> list[list[Json]]:
    """Rows of checked cells."""
    if not isinstance(value, list) or any(not isinstance(row, list) for row in value):
        raise ValueError("output rows are not a list of rows")
    return [[checked_cell(cell) for cell in row] for row in value]


def submultiset(rows: list[list[Json]], available: list[list[Json]]) -> bool:
    """Whether each row occurs in `available`, each occurrence used once."""
    remaining = list(available)
    for row in rows:
        if row not in remaining:
            return False
        remaining.remove(row)
    return True


def matches_groups(groups: list[dict[str, Json]], rows: list[list[Json]]) -> bool:
    """Whether the rows are, in order, a selection of `count` rows from each group."""
    for group in groups:
        count, eligible = group["count"], rows_of(group["rows"])
        if type(count) is not int or not 0 < count <= len(eligible) or count > len(rows):
            return False
        if not submultiset(rows[:count], eligible):
            return False
        rows = rows[count:]
    return not rows


def matches_output(expected: dict[str, Json], actual: dict[str, Json], groups: Json) -> bool:
    """Whether a predicted output agrees with the recorded one; the recorded one must be valid too."""
    columns = expected["columns"]
    expected_rows, actual_rows = rows_of(expected["rows"]), rows_of(actual["rows"])
    if (any(len(row) != len(columns) for row in expected_rows) or any(len(row) != len(columns) for row in actual_rows)
            or actual["columns"] != columns or actual["changes"] != expected["changes"]):
        return False
    if groups is None:
        return len(expected_rows) == len(actual_rows) and submultiset(actual_rows, expected_rows)
    if not isinstance(groups, list) or not groups:
        return False
    if any(group["count"] != len(rows_of(group["rows"])) for group in groups[1:-1]):
        return False  # Only the first and last group can be cut by a window.
    if any(len(row) != len(columns) for group in groups for row in rows_of(group["rows"])):
        return False
    return matches_groups(groups, expected_rows) and matches_groups(groups, actual_rows)
