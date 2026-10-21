"""Authored coverage cases of DISTINCT, HAVING and aggregates inside expressions (ADR 0018, slice 3).

The cases follow the "Tests" list of the slice 3 task: aggregates in arithmetic and comparisons,
over groups and over an empty table; `HAVING` with and without `GROUP BY`, with an aggregate that
is not a result column; `ORDER BY` by an aggregate; `DISTINCT` over integers, text with `NOCASE`
whose duplicates are equal, NULLs, and with `ORDER BY` and `LIMIT`; and the prepare errors of
`HAVING` on a non-aggregate query and of a nested aggregate. Native SQLite is the only source of
outcomes. The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE t(g, v INTEGER, s TEXT COLLATE NOCASE); "
          "INSERT INTO t VALUES(1, 10, 'a'), (1, 20, 'a'), (2, 5, 'b'), (3, NULL, 'c'), (3, NULL, NULL), (4, 7, NULL); "
          "CREATE TABLE e(x);")
"""A table whose groups have two rows, one row, NULL values and NULL text, whose text compares
under NOCASE with duplicates that are the same bytes; and an empty table."""

AGGREGATE_QUERY = "R-20637-43463"
"""SQLite: a SELECT is an aggregate query if it has GROUP BY or an aggregate in the result set."""
HAVING = "R-31537-00101"
"""SQLite: HAVING is evaluated once for each group, and a false result discards the group."""
HAVING_AGGREGATE = "R-04132-09474"
"""SQLite: an aggregate HAVING expression is evaluated across all rows in the group."""
HAVING_HIDDEN = "R-55403-13450"
"""SQLite: HAVING may refer to aggregates that are not in the result."""
DISTINCT = "R-14442-41305"
"""SQLite: SELECT DISTINCT removes duplicate rows from the result."""
ALL = "R-01256-01950"
"""SQLite: without ALL or DISTINCT, the behavior is that of ALL."""
SUM = "R-24943-34514"
"""SQLite: sum() and total() return the sum of all non-NULL values in the group."""


def definitions() -> list[QueryCase]:
    """The coverage cases of DISTINCT, HAVING and aggregates inside expressions."""
    case = QueryCase
    return [
        case("group-aggregate-arithmetic", TABLES,
             "SELECT g, count(*) + 1, sum(v) * 2, max(v) - min(v), count(v) = count(*) FROM t GROUP BY g ORDER BY g;",
             (AGGREGATE_QUERY, SUM), ("aggregate", "expression")),
        case("group-aggregate-empty", TABLES,
             "SELECT count(*) + 1, max(x) IS NULL, total(x) * 2 FROM e;", (AGGREGATE_QUERY,),
             ("aggregate", "expression", "empty")),
        case("group-having", TABLES,
             "SELECT g, count(*) FROM t GROUP BY g HAVING count(*) > 1 OR g = 4 ORDER BY g;",
             (HAVING, HAVING_AGGREGATE), ("having",)),
        case("group-having-hidden", TABLES,
             "SELECT g FROM t GROUP BY g HAVING sum(v) > 6 ORDER BY g;", (HAVING, HAVING_HIDDEN), ("having",)),
        case("group-having-null", TABLES,
             "SELECT g FROM t GROUP BY g HAVING max(v) > 6 ORDER BY g;", (HAVING,), ("having", "null")),
        case("group-having-without-group-by", TABLES,
             "SELECT count(*) FROM t HAVING count(*) > 1; SELECT count(*) FROM e HAVING count(*) > 0;",
             (HAVING, AGGREGATE_QUERY), ("having",)),
        case("group-order-by-aggregate", TABLES,
             "SELECT g, sum(v) AS total FROM t GROUP BY g ORDER BY total DESC, g;", (AGGREGATE_QUERY,), ("order-by", "aggregate")),
        case("distinct-values", TABLES,
             "SELECT DISTINCT g FROM t ORDER BY g; SELECT DISTINCT s FROM t ORDER BY s; SELECT DISTINCT v IS NULL FROM t "
             "ORDER BY 1; SELECT ALL g FROM t ORDER BY g;",
             (DISTINCT, ALL), ("distinct",)),
        case("distinct-window", TABLES,
             "SELECT DISTINCT g FROM t ORDER BY g DESC LIMIT 2 OFFSET 1;", (DISTINCT,), ("distinct", "limit")),
        case("distinct-aggregate", TABLES,
             "SELECT DISTINCT count(*) FROM t GROUP BY g ORDER BY 1;", (DISTINCT, AGGREGATE_QUERY),
             ("distinct", "aggregate")),
        case("having-non-aggregate", TABLES, "SELECT v FROM t HAVING v > 1;", (HAVING,), ("having", "error")),
        case("aggregate-nested", TABLES, "SELECT sum(count(*)) FROM t;", (AGGREGATE_QUERY,), ("aggregate", "error")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `distinct-having`."""
    return query_records(definitions() if cases is None else cases, part="distinct-having")
