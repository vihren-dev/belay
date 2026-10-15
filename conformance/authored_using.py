"""Authored coverage cases of USING and NATURAL joins (ADR 0012, amendment 2, slice 4b).

The cases follow the "Tests" list of the slice 4b task: `USING` with one and two names,
in inner, left and comma joins; `NATURAL` inner and left joins with one, two and no
common columns; `*`, `x.*`, and qualified and unqualified merged names in result
columns, `WHERE`, `GROUP BY` and `ORDER BY`; a merged name for a padded row; the
left-most left column of an earlier source; a self-join; the ambiguity with a third
source; and the prepare errors and their order. Native SQLite is the only source of
outcomes. The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE t(a INTEGER, b TEXT); CREATE TABLE u(A INTEGER, c TEXT); "
          "CREATE TABLE v(a INTEGER, b TEXT, d TEXT); CREATE TABLE z(q INTEGER); "
          "INSERT INTO t VALUES(1, 'x'), (2, 'y'); INSERT INTO u VALUES(1, 'p'), (3, 'q'); "
          "INSERT INTO v VALUES(1, 'x', 'm'), (2, 'z', 'n'); INSERT INTO z VALUES(9);")
"""Four tables: `t` and `u` share `a` (declared `A` in `u`); `t` and `v` share `a` and `b`;
`z` shares no name with `t`. Row 2 of `t` matches no row of `u`, and row 2 of `v` matches
`t` on `a` but not on `b`."""

CONDITION = "R-54152-55276"
"""SQLite: for each pair of named columns, `lhs.X = rhs.X` must be true."""
OMITTED = "R-57047-10461"
"""SQLite: the right column of each pair of a USING clause is omitted from the dataset."""
NATURAL = "R-04932-55942"
"""SQLite: NATURAL adds an implicit USING of the column names of both inputs."""
LEFT = "R-24610-05866"
"""SQLite: a left join adds each unmatched left row, after the ON or USING filter."""
NAMES = "R-48861-28451"
"""SQLite: the tables of FROM are joined into one dataset for the SELECT to operate on."""
MISSING = "R-49933-05137"
"""SQLite: each name of USING must exist in the datasets left and right of the join."""
NATURAL_CLAUSE = "R-39625-59133"
"""SQLite: a NATURAL join may not have a USING or ON clause."""


def definitions() -> list[QueryCase]:
    """The coverage cases of USING and NATURAL joins."""
    case = QueryCase
    return [
        case("using-inner", TABLES, "SELECT * FROM t JOIN u USING (a);", (CONDITION, OMITTED), ("using", "inner")),
        case("using-left", TABLES, "SELECT * FROM t LEFT JOIN u USING (a);", (LEFT, OMITTED), ("using", "left")),
        case("using-left-merged-names", TABLES, "SELECT a, t.a, u.a FROM t LEFT JOIN u USING (a);", (LEFT, OMITTED),
             ("using", "left", "names")),
        case("using-two-names", TABLES, "SELECT * FROM t JOIN v USING (a, b);", (CONDITION, OMITTED),
             ("using", "two")),
        case("using-comma", TABLES, "SELECT * FROM t, u USING (a);", (CONDITION,), ("using", "comma")),
        case("using-source-star", TABLES, "SELECT u.*, t.* FROM t JOIN u USING (\"A\");", (OMITTED,),
             ("using", "star")),
        case("using-clauses", TABLES,
             "SELECT a, count(*) FROM t LEFT JOIN u USING (a) WHERE a > 0 GROUP BY a ORDER BY 1 DESC;", (NAMES,),
             ("using", "where", "group-by", "order-by")),
        case("using-order-by-merged", TABLES, "SELECT a, b, c FROM t LEFT JOIN u USING (a) ORDER BY a DESC;", (NAMES,),
             ("using", "order-by")),
        case("using-self-join", TABLES, "SELECT * FROM t JOIN t AS x USING (a);", (CONDITION,), ("using", "self")),
        case("using-twice", TABLES, "SELECT * FROM t JOIN u USING (a) JOIN v USING (a);", (CONDITION, OMITTED),
             ("using", "three")),
        case("natural-two-common", TABLES, "SELECT * FROM t NATURAL JOIN v;", (NATURAL,), ("natural", "inner")),
        case("natural-left", TABLES, "SELECT * FROM t natural Left Join v;", (NATURAL, LEFT), ("natural", "left")),
        case("natural-one-common", TABLES, "SELECT * FROM u NATURAL JOIN t;", (NATURAL,), ("natural", "names")),
        case("natural-no-common", TABLES, "SELECT * FROM t NATURAL JOIN z;", ("R-49566-01570",),
             ("natural", "cross")),
        case("natural-left-most", TABLES, "SELECT * FROM t, u NATURAL JOIN v;", (NATURAL,), ("natural", "three")),
        case("using-ambiguous-third", TABLES, "SELECT * FROM t LEFT JOIN u USING (a) JOIN v ON a = v.a;", (NAMES,),
             ("using", "prepare-error", "ambiguous")),
        case("using-missing-column", TABLES, "SELECT * FROM t JOIN u USING (b);", (MISSING,),
             ("using", "prepare-error")),
        case("using-rowid", TABLES, "SELECT * FROM t JOIN u USING (rowid);", (MISSING,), ("using", "prepare-error")),
        case("natural-with-on", TABLES, "SELECT * FROM t NATURAL JOIN u ON t.a = u.a;", (NATURAL_CLAUSE,),
             ("natural", "prepare-error")),
        case("natural-with-using", TABLES, "SELECT * FROM t NATURAL JOIN u USING (a);", (NATURAL_CLAUSE,),
             ("natural", "prepare-error")),
        case("using-error-after-missing-table", TABLES, "SELECT * FROM t JOIN u USING (q) JOIN zz;", (MISSING,),
             ("using", "prepare-error", "order")),
        case("using-error-before-result", TABLES, "SELECT zz FROM t JOIN u USING (q);", (MISSING,),
             ("using", "prepare-error", "order")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `using`."""
    return query_records(definitions() if cases is None else cases, part="using")
