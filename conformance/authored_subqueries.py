"""Authored coverage cases of subqueries (ADR 0018, slice 1).

The cases follow the "Tests" list of the slice 1 task: `EXISTS` and `NOT EXISTS`, `IN` and
`NOT IN` with NULLs, affinity and collation, scalar subqueries with no row, one row and a
certain first row, correlation at depth one and two, a name of the subquery's own table
that hides an outer column, aggregates inside a subquery, subqueries in `ORDER BY`, in a join
and without `FROM`, subqueries in `UPDATE`, `DELETE` and `INSERT ... VALUES`, and the prepare
errors of a subquery with two result columns. Native
SQLite is the only source of outcomes. The cases use `conformance.authored_queries.QueryCase`
and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE t(k INTEGER, v TEXT); INSERT INTO t VALUES(1, 'a'), (2, 'b'), (NULL, 'c'), (3, 'A'); "
          "CREATE TABLE u(x, s TEXT COLLATE NOCASE, k); "
          "INSERT INTO u VALUES(1, 'A', 9), (NULL, 'b', NULL), (3, 'z', NULL), (1, 'q', NULL); "
          "CREATE TABLE w(s TEXT); INSERT INTO w VALUES('1');")
"""A table {k, v}; a table {x, s, k} whose `x` has a NULL and a repeated value, whose `s`
compares under NOCASE, and whose `k` hides `t.k` inside its subqueries; and one TEXT row `'1'`."""

SUBQUERY = "R-43573-23448"
"""SQLite: a SELECT statement enclosed in parentheses is a subquery."""
FIRST_ROW = "R-18318-14995"
"""SQLite: the value of a subquery expression is the first row of the result."""
NO_ROW = "R-52325-25449"
"""SQLite: the value of a subquery expression is NULL if the SELECT returns no rows."""
EXISTS_ONE = "R-58553-63740"
"""SQLite: EXISTS is 1 if the SELECT would return one or more rows."""
EXISTS_ZERO = "R-19673-40972"
"""SQLite: EXISTS is 0 if the SELECT would return no rows."""
EXISTS_COLUMNS = "R-35109-49139"
"""SQLite: the number of columns and the values have no effect on EXISTS."""
CORRELATED = "R-25616-08788"
"""SQLite: a scalar subquery or the operand of IN or EXISTS may refer to columns of the outer query."""
REEVALUATED = "R-45820-61953"
"""SQLite: a correlated subquery is reevaluated each time its result is required."""
IN_MATRIX = "R-50221-42915"
"""SQLite: the result of IN and NOT IN follows the matrix of NULL, empty and found operands."""
IN_AFFINITY = "R-24564-50022"
"""SQLite: the right operand of IN has the affinity of the result set expression of its SELECT."""
IN_SCALAR = "R-35033-20570"
"""SQLite: the subquery of IN must be a scalar subquery if the left expression is not a row value."""
COLUMN_TYPE = "R-27438-53558"
"""SQLite: each column of a subquery has the collation and affinity of its expression."""
AGGREGATE = "R-56294-03966"
"""SQLite: aggregate queries are allowed as scalar subqueries."""


def definitions() -> list[QueryCase]:
    """The coverage cases of subqueries."""
    case = QueryCase
    return [
        case("subquery-exists-correlated", TABLES,
             "SELECT k FROM t WHERE EXISTS (SELECT 1 FROM u WHERE u.x = t.k) ORDER BY k;",
             (SUBQUERY, EXISTS_ONE, CORRELATED, REEVALUATED), ("subquery", "exists", "correlated")),
        case("subquery-not-exists", TABLES,
             "SELECT v FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE x = t.k) ORDER BY v;",
             (EXISTS_ZERO, CORRELATED), ("subquery", "exists", "not")),
        case("subquery-exists-values", TABLES,
             "SELECT k, EXISTS (SELECT x, s FROM u WHERE x = t.k), EXISTS (SELECT 1 FROM u WHERE 0) FROM t ORDER BY k;",
             (EXISTS_ONE, EXISTS_ZERO, EXISTS_COLUMNS), ("subquery", "exists", "value")),
        case("subquery-in-nulls", TABLES,
             "SELECT k, k IN (SELECT x FROM u), k NOT IN (SELECT x FROM u) FROM t ORDER BY k;",
             (IN_MATRIX,), ("subquery", "in", "null")),
        case("subquery-in-without-nulls", TABLES,
             "SELECT k, k IN (SELECT x FROM u WHERE x IS NOT NULL), k NOT IN (SELECT x FROM u WHERE x IS NOT NULL), "
             "k IN (SELECT x FROM u WHERE 0), k NOT IN (SELECT x FROM u WHERE 0) FROM t ORDER BY k;",
             (IN_MATRIX,), ("subquery", "in", "empty")),
        case("subquery-in-affinity", TABLES,
             "SELECT 1 IN (SELECT s FROM w), '1' IN (SELECT x FROM u), (SELECT s FROM w) = 1, "
             "(SELECT s FROM w) IN (SELECT 1);",
             (IN_AFFINITY, COLUMN_TYPE), ("subquery", "in", "affinity")),
        case("subquery-in-collation", TABLES,
             "SELECT v, 'a' IN (SELECT s FROM u), 'a' IN (SELECT s COLLATE BINARY FROM u), v IN (SELECT s FROM u) "
             "FROM t ORDER BY v;",
             (COLUMN_TYPE,), ("subquery", "in", "collation")),
        case("subquery-scalar-aggregate", TABLES,
             "SELECT k, (SELECT max(x) FROM u WHERE x <= t.k), (SELECT count(*) FROM u WHERE x = t.k) FROM t ORDER BY k;",
             (FIRST_ROW, AGGREGATE, CORRELATED), ("subquery", "scalar", "aggregate")),
        case("subquery-scalar-no-row", TABLES,
             "SELECT k, (SELECT s FROM u WHERE x = t.k + 10) FROM t ORDER BY k;",
             (NO_ROW,), ("subquery", "scalar", "empty")),
        case("subquery-scalar-one-row", TABLES,
             "SELECT k, (SELECT s FROM u WHERE x = t.k AND s <> 'q') FROM t ORDER BY k;",
             (FIRST_ROW, NO_ROW, CORRELATED), ("subquery", "scalar", "lookup")),
        case("subquery-scalar-first-row", TABLES,
             "SELECT (SELECT s FROM u WHERE x IS NOT NULL ORDER BY x DESC, s), (SELECT s FROM u ORDER BY x DESC);",
             (FIRST_ROW,), ("subquery", "scalar", "order-by")),
        case("subquery-depth-two", TABLES,
             "SELECT k FROM t WHERE EXISTS (SELECT 1 FROM u WHERE u.x = 3 AND "
             "EXISTS (SELECT 1 FROM u AS i WHERE i.x = t.k)) ORDER BY k;",
             (CORRELATED,), ("subquery", "correlated", "nested")),
        case("subquery-own-name-first", TABLES,
             "SELECT v FROM t WHERE EXISTS (SELECT 1 FROM u WHERE k = 9) ORDER BY v;",
             (CORRELATED,), ("subquery", "name", "scope")),
        case("subquery-in-aggregate-query", TABLES,
             "SELECT count(*), sum(k) FROM t WHERE k IN (SELECT x FROM u);",
             (IN_MATRIX,), ("subquery", "in", "aggregate")),
        case("subquery-order-by", TABLES,
             "SELECT v, (SELECT count(*) FROM u WHERE x = t.k) AS n FROM t ORDER BY n DESC, v;",
             (CORRELATED, REEVALUATED), ("subquery", "order-by")),
        case("subquery-join", TABLES,
             "SELECT t.k, u.s FROM t JOIN u ON t.k = u.x WHERE u.s <> (SELECT s FROM w) ORDER BY 1, 2;",
             (FIRST_ROW,), ("subquery", "join")),
        case("subquery-without-from", TABLES,
             "SELECT EXISTS (SELECT 1 FROM u), (SELECT count(*) FROM t), 3 IN (SELECT x FROM u);",
             (EXISTS_ONE, AGGREGATE, IN_MATRIX), ("subquery", "fromless")),
        case("subquery-update-set", TABLES,
             "UPDATE t SET v = (SELECT s FROM u WHERE x = t.k AND s <> 'q'); SELECT k, v FROM t ORDER BY k;",
             (FIRST_ROW, NO_ROW, CORRELATED), ("subquery", "update")),
        case("subquery-update-where", TABLES,
             "UPDATE t SET v = 'hit' WHERE k IN (SELECT x FROM u); SELECT k, v FROM t ORDER BY k;",
             (IN_MATRIX,), ("subquery", "update", "in")),
        case("subquery-delete-where", TABLES,
             "DELETE FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE x = t.k); SELECT k FROM t ORDER BY k;",
             (EXISTS_ZERO, CORRELATED), ("subquery", "delete")),
        case("subquery-insert-values", TABLES,
             "INSERT INTO w VALUES ((SELECT count(*) FROM u)), ((SELECT max(s) FROM u)); SELECT s FROM w ORDER BY s;",
             (FIRST_ROW, AGGREGATE), ("subquery", "insert")),
        case("subquery-scalar-columns", TABLES, "SELECT (SELECT x, s FROM u);", (IN_SCALAR,),
             ("subquery", "scalar", "error")),
        case("subquery-in-columns", TABLES, "SELECT k FROM t WHERE k IN (SELECT x, s FROM u);", (IN_SCALAR,),
             ("subquery", "in", "error")),
        case("subquery-no-such-column", TABLES, "SELECT k FROM t WHERE EXISTS (SELECT 1 FROM u WHERE z = 1);",
             (SUBQUERY,), ("subquery", "error")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `subqueries`."""
    return query_records(definitions() if cases is None else cases, part="subqueries")
