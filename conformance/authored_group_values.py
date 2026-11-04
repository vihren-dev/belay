"""Native inputs for the values of a group of an aggregate query (ADR 0030, slice 2).

The cases follow "The row of a group" of the ADR: without `min` or `max` every expression reads
the first row of the group; the last distinct `min` or `max` call in the order result columns,
`ORDER BY`, `HAVING` decides the row; a result column associated with a grouping term by number or
alias gives the term's value on the first row unless it is a column under at most `COLLATE`. The
plan of every case reads the rows in rowid order, so the first row of a group does not depend on an
index. The recorder observes the order of rows only by projected sort keys, so a case with a call
in `ORDER BY` puts the query in a derived table and compares its rows without order. No case
orders by an associated result column of a query with two or more grouping terms: SQLite's plan
then reads that column from the row of the group, a rule that the ADR does not know (issue #309).
`INSERT ... SELECT` from a grouped source is outside the subject's scope. SQLite supplies every
outcome through the query recorder.
"""

from conformance.authored_queries import QueryCase
from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.native_record import record_sql

ROWS = ("CREATE TABLE t(a, c TEXT COLLATE NOCASE, n); "
        "INSERT INTO t VALUES(1.0, 'a', 1), (1, 'A', 3), (1, 'A', 2), (2, 'B', 4), (2, 'b', 6), (2, 'B', 5);")
"""Two groups under `c`: in the first, the first row is `'a'` and the maximum's row `'A'`; in the
second, the first row and the minimum's row are `'B'` and the maximum's row is `'b'`. `a+0` puts
`1.0` and `1` in one group."""
NUMBERS = "CREATE TABLE u(k, v); INSERT INTO u VALUES(1.0, 'z'), (1, 'a'), (1.0, 'm'), (2, 2), (2.0, 2.0);"
"""Groups of `k` whose rows differ in storage class: the minimum of `v` is on a later row, and a
tie of `2` and `2.0` keeps the first row."""
NULLS = ("CREATE TABLE w(a, c TEXT COLLATE NOCASE, n); "
         "INSERT INTO w VALUES(1.0, 'a', NULL), (1, 'A', NULL), (3, 'x', NULL), (3, 'X', 7), (3, 'x', NULL);")
"""A group whose `n` is NULL on every row, and a group whose one value of `n` is between NULLs."""
TIES = "CREATE TABLE v(c TEXT COLLATE NOCASE, n); INSERT INTO v VALUES('a', 1), ('A', 3), ('a', 3), ('B', 1), ('b', 1);"
"""Ties of the maximum and of the minimum on rows that differ in `c`."""

ARBITRARY_ROW = "R-62913-19830"
"""SQLite: a non-aggregate expression of an aggregate query is evaluated against a single row of the group."""


def definitions() -> list[QueryCase]:
    """The cases: the queries of "What the model gives today", the deciding call in each clause and
    order, repeated calls in other spellings and with unary plus, ties, NULL operands, associated result columns by number and alias with
    `COLLATE`, unary plus and `CAST`, and the result read by a derived table and a compound."""
    def case(name: str, sql: str, *features: str, setup: str = ROWS) -> QueryCase:
        """Give a case its name prefix, requirement and features."""
        return QueryCase("group-values-" + name, setup, sql, (ARBITRARY_ROW,), ("group-by", *features))

    return [
        case("max", "SELECT c, max(n) FROM t GROUP BY c ORDER BY 2;", "max"),
        case("max-expression", "SELECT c || '', max(n) FROM t GROUP BY c ORDER BY 2;", "max"),
        case("max-in-having", "SELECT c FROM t GROUP BY c HAVING max(n) > 0 ORDER BY 1;", "max", "having"),
        case("min-later-row", "SELECT k, typeof(k), min(v) FROM u GROUP BY k ORDER BY 1;", "min", setup=NUMBERS),
        case("max-then-min", "SELECT c, max(n), min(n) FROM t GROUP BY c ORDER BY 2;", "max", "min"),
        case("min-then-max", "SELECT c, min(n), max(n) FROM t GROUP BY c ORDER BY 3;", "max", "min"),
        case("order-after-result", "SELECT * FROM (SELECT c, max(n) FROM t GROUP BY c ORDER BY min(n));", "max",
             "min", "order-by"),
        case("having-after-order", "SELECT * FROM (SELECT c FROM t GROUP BY c HAVING min(n) > 0 ORDER BY max(n));",
             "having", "order-by"),
        case("order-before-having", "SELECT * FROM (SELECT c FROM t GROUP BY c HAVING max(n) > 0 ORDER BY min(n));",
             "having", "order-by"),
        case("repeated-call", "SELECT c, max(n), min(n), max(n) AS again FROM t GROUP BY c ORDER BY 3;", "repeated"),
        case("repeated-other-spelling", "SELECT c, max(n), min(n), MAX(t.n) AS again FROM t GROUP BY c ORDER BY 3;",
             "repeated"),
        case("repeated-with-plus", "SELECT c, max(n), min(n), max(+n) FROM t GROUP BY c ORDER BY 3;", "repeated", "plus"),
        case("repeated-integer-spelling", "SELECT c, max(n+1), min(n), max(n+01) AS again FROM t GROUP BY c ORDER BY 3;",
             "repeated"),
        case("repeated-real-spelling", "SELECT c, max(n+1.0), min(n), max(n+1.00) AS again FROM t GROUP BY c ORDER BY 3;",
             "repeated"),
        case("repeated-in-having", "SELECT c, min(n), max(n) FROM t GROUP BY c HAVING min(n) > 0 ORDER BY 3;",
             "repeated", "having"),
        case("other-aggregates", "SELECT c, count(*), sum(n), max(n) FROM t GROUP BY c ORDER BY 4;", "max"),
        case("no-min-or-max", "SELECT c, count(*) FROM t GROUP BY c ORDER BY 2, 1;", "first-row"),
        case("tie-of-maximum", "SELECT c, max(n) FROM v GROUP BY c ORDER BY 2;", "tie", setup=TIES),
        case("tie-of-minimum", "SELECT c, min(n), count(*) FROM v GROUP BY c ORDER BY 3;", "tie", setup=TIES),
        case("tie-of-numbers", "SELECT k, typeof(k), max(v) FROM u GROUP BY k ORDER BY 1;", "tie", setup=NUMBERS),
        case("null-operand", "SELECT a+0, c, max(n) FROM w GROUP BY 1, c ORDER BY 3;", "null", setup=NULLS),
        case("null-then-value", "SELECT c, min(n) FROM w GROUP BY c ORDER BY 1;", "null", setup=NULLS),
        case("having-reads-row", "SELECT count(*) FROM t GROUP BY c HAVING c || '' = 'A' AND max(n) > 0;", "having"),
        case("having-reads-min-row", "SELECT count(*) FROM t GROUP BY c HAVING c || '' = 'a' AND min(n) > 0;",
             "having"),
        case("number-twice", "SELECT a+0, a+0 AS b, max(n) FROM t GROUP BY 1 ORDER BY 3;", "association", "number"),
        case("number-names-column", "SELECT c, max(n) FROM t GROUP BY 1 ORDER BY 2;", "association", "number"),
        case("alias-twice", "SELECT a+0 AS k, a+0, max(n) FROM t GROUP BY k ORDER BY 3;", "association", "alias"),
        case("alias-of-last", "SELECT a+0, a+0 AS k, max(n) FROM t GROUP BY k ORDER BY 3;", "association", "alias"),
        case("alias-name-case", "SELECT a+0 AS k, A + 0, max(n) FROM t GROUP BY k ORDER BY 3;", "association",
             "alias"),
        case("alias-qualified", "SELECT a+0 AS k, t.a+0, max(n) FROM t GROUP BY k ORDER BY 3;", "association",
             "alias"),
        case("plus-one-side", "SELECT +c AS k, c, max(n) FROM t GROUP BY k ORDER BY 3;", "association", "plus"),
        case("plus-both-sides", "SELECT +c AS k, +c, max(n) FROM t GROUP BY k ORDER BY 3;", "association", "plus"),
        case("collate-one-side", "SELECT CAST(c AS TEXT) COLLATE NOCASE AS k, CAST(c AS TEXT), max(n) FROM t "
             "GROUP BY k ORDER BY 3;", "association", "collate"),
        case("collate-both-sides", "SELECT CAST(c AS TEXT) COLLATE NOCASE AS k, CAST(c AS TEXT) COLLATE NOCASE, "
             "max(n) FROM t GROUP BY k ORDER BY 3;", "association", "collate"),
        case("collated-column", "SELECT c COLLATE NOCASE AS k, max(n) FROM t GROUP BY k ORDER BY 2;", "association",
             "collate"),
        case("cast-name-case", "SELECT CAST(c AS TEXT) AS k, CAST(c AS text), max(n) FROM t GROUP BY k ORDER BY 3;",
             "association", "cast"),
        case("cast-same-name", "SELECT CAST(c AS TEXT) AS k, CAST(c AS TEXT), max(n) FROM t GROUP BY k ORDER BY 3;",
             "association", "cast"),
        case("derived-table", "SELECT x, m FROM (SELECT c AS x, max(n) AS m FROM t GROUP BY c) ORDER BY m;",
             "subquery"),
        case("compound", "SELECT c FROM t GROUP BY c HAVING max(n) > 0 UNION ALL SELECT 'z' ORDER BY 1;",
             "compound"),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 7 record under SQLite's default measured profile."""
    selected = definitions() if cases is None else cases
    defaults = profile(())
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=defaults, run_on=True, counters=True),
             "part": "group-values", "features": list(case.features)}
            for case in selected]
