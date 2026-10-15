"""Authored coverage cases of RIGHT and FULL joins (ADR 0012, amendment 3, slice 4c).

The cases follow Amendment 3, "Testing", for slice 4c: right and full joins with matched
and unmatched rows on both sides, with no `ON`, with `ON` true for no row, with an empty
input, after an inner and a left join, before a left join, two full joins in a row; a
right join of a comma join; `WHERE` on a padded column; aggregates and `GROUP BY` over
padded rows; qualified and unqualified names, `*` and `x.*`; and `ORDER BY`. Native
SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE t(a INTEGER, b TEXT); CREATE TABLE u(a INTEGER, c TEXT); CREATE TABLE v(a INTEGER, d TEXT); "
          "CREATE TABLE e(a INTEGER); "
          "INSERT INTO t VALUES(1, 'x'), (2, 'y'); INSERT INTO u VALUES(1, 'p'), (3, 'q'); "
          "INSERT INTO v VALUES(3, 'm'), (4, 'n');")
"""Four tables: row 1 of `t` and `u` match on `a`, row 2 of `t` and row 3 of `u` match
nothing; `v` matches row 3 of `u`; `e` is empty."""

RIGHT = "R-15753-04279"
"""SQLite: a right join adds each unmatched right row, after the ON filter."""
FULL = "R-18902-30764"
"""SQLite: a full join is a combination of a left and a right join."""
NAMES = "R-48861-28451"
"""SQLite: the tables of FROM are joined into one dataset for the SELECT to operate on."""


def definitions() -> list[QueryCase]:
    """The coverage cases of RIGHT and FULL joins."""
    case = QueryCase
    return [
        case("right-on", TABLES, "SELECT * FROM t RIGHT JOIN u ON t.a = u.a;", (RIGHT,), ("right",)),
        case("right-outer-keywords", TABLES, "SELECT t.b, u.c FROM t right Outer join u ON t.a = u.a;", (RIGHT,),
             ("right", "outer")),
        case("full-on", TABLES, "SELECT * FROM t FULL JOIN u ON t.a = u.a;", (FULL,), ("full",)),
        case("full-outer", TABLES, "SELECT t.b, u.c FROM t FULL OUTER JOIN u ON t.a = u.a;", (FULL,),
             ("full", "outer")),
        case("right-without-on", TABLES, "SELECT * FROM t RIGHT JOIN u;", (RIGHT,), ("right", "product")),
        case("full-on-false", TABLES, "SELECT * FROM t FULL JOIN u ON t.a = u.a AND t.a > 5;", (FULL,),
             ("full", "no-match")),
        case("right-empty-left", TABLES, "SELECT * FROM e RIGHT JOIN u ON e.a = u.a;", (RIGHT,), ("right", "empty")),
        case("full-empty-right", TABLES, "SELECT * FROM t FULL JOIN e ON t.a = e.a;", (FULL,), ("full", "empty")),
        case("right-after-inner", TABLES, "SELECT * FROM t JOIN u ON t.a = u.a RIGHT JOIN v ON u.a = v.a;", (RIGHT,),
             ("right", "three")),
        case("right-after-left", TABLES, "SELECT * FROM t LEFT JOIN u ON t.a = u.a RIGHT JOIN v ON v.a = u.a;",
             (RIGHT,), ("right", "left", "three")),
        case("right-before-left", TABLES, "SELECT * FROM t RIGHT JOIN u ON t.a = u.a LEFT JOIN v ON v.a = u.a;",
             (RIGHT,), ("right", "left", "three")),
        case("two-full", TABLES, "SELECT * FROM t FULL JOIN u ON t.a = u.a FULL JOIN v ON v.a = u.a;", (FULL,),
             ("full", "three")),
        case("right-of-comma", TABLES, "SELECT * FROM t, u RIGHT JOIN v ON v.a = u.a;", (RIGHT,),
             ("right", "comma")),
        case("right-on-first-table", TABLES, "SELECT * FROM t, u RIGHT JOIN v ON v.a = t.a;", (RIGHT,),
             ("right", "comma", "no-match")),
        case("right-where-padded", TABLES, "SELECT u.c FROM t RIGHT JOIN u ON t.a = u.a WHERE t.a IS NULL;",
             (RIGHT,), ("right", "where")),
        case("full-aggregates", TABLES, "SELECT count(*), count(t.a), count(u.a) FROM t FULL JOIN u ON t.a = u.a;",
             (FULL,), ("full", "aggregate")),
        case("full-group-by", TABLES,
             "SELECT u.c, count(t.b) FROM t FULL JOIN u ON t.a = u.a GROUP BY u.c ORDER BY 1;", (FULL,),
             ("full", "group-by")),
        case("right-source-star", TABLES, "SELECT u.*, t.* FROM t RIGHT JOIN u ON t.a = u.a;", (NAMES,),
             ("right", "star")),
        case("right-unqualified", TABLES, "SELECT b, c FROM t RIGHT JOIN u ON t.a = u.a;", (NAMES,),
             ("right", "names")),
        case("right-order-by", TABLES, "SELECT u.a, t.b FROM t RIGHT JOIN u ON t.a = u.a ORDER BY u.a DESC;",
             (NAMES,), ("right", "order-by")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `right`."""
    return query_records(definitions() if cases is None else cases, part="right")
