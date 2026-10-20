"""Authored coverage cases of the aggregates `group_concat`, `string_agg` and `total` (ADR 0015,
slice 5).

The cases follow the "Tests" list of the slice 5 task: values of each type, a separator per
row and a NULL separator, empty and all-NULL groups, the order of the rows of a group with
GROUP BY, and `total` over integers whose sum overflows. Native SQLite is the only source of
outcomes. The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE a(k INTEGER PRIMARY KEY, g INTEGER, v, s TEXT, n INTEGER); "
          "INSERT INTO a VALUES (1, 1, 'b', '-', 9223372036854775807), (2, 2, 7, NULL, 1), "
          "(3, 1, 2.5, '+', 1), (4, 1, NULL, '*', -5), (5, 2, x'4142', '', NULL), (6, 3, NULL, '/', NULL), "
          "(7, 1, '', ';', 2);")
"""One table with three groups: values of each type in insertion order that differs from the
value order, an empty string, separators per row (one NULL, one empty), an all-NULL group,
and integers whose sum overflows."""

GROUP_CONCAT = "R-56088-25150"
"""SQLite: the group_concat() function returns a string which is the concatenation of all
non-NULL values of X."""
SEPARATOR = "R-08600-21007"
"""SQLite: if parameter Y is present then it is used as the separator between instances of X."""
COMMA = "R-39910-14723"
"""SQLite: a comma is used as the separator if Y is omitted."""
STRING_AGG = "R-07264-38747"
"""SQLite: the string_agg(X,Y) function is an alias for group_concat(X,Y)."""
TOTAL = "R-24943-34514"
"""SQLite: the sum() and total() aggregate functions return the sum of all non-NULL values in
the group."""
TOTAL_REAL = "R-07734-01023"
"""SQLite: the result of total() is always a floating point value."""
TOTAL_EMPTY = "R-44223-43966"
"""SQLite: if there are no non-NULL input rows then sum() returns NULL but total() returns 0."""


def definitions() -> list[QueryCase]:
    """The coverage cases of slice 5 of ADR 0015."""
    case = QueryCase
    return [
        case("aggregate-group-concat", TABLES, "SELECT g AS n, group_concat(v), group_concat(v, s), string_agg(v, s), "
             "group_concat(v, '') FROM a GROUP BY g ORDER BY n;", (GROUP_CONCAT, SEPARATOR, COMMA, STRING_AGG),
             ("functions", "group_concat", "string_agg", "group-by")),
        case("aggregate-group-concat-table", TABLES, "SELECT group_concat(k), group_concat(v, NULL), "
             "group_concat(s, k) FROM a; "
             "SELECT group_concat(v), string_agg(v, ',') FROM a WHERE k > 9;", (GROUP_CONCAT, SEPARATOR),
             ("functions", "group_concat", "empty-table")),
        case("aggregate-total", TABLES, "SELECT g AS m, total(n), total(v), sum(v) FROM a GROUP BY g ORDER BY m; "
             "SELECT total(n), total(k) FROM a; SELECT total(n) FROM a WHERE k > 9;",
             (TOTAL, TOTAL_REAL, TOTAL_EMPTY), ("functions", "total", "integer-overflow")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `aggregates`."""
    return query_records(definitions() if cases is None else cases, part="aggregates")
