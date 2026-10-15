"""Authored coverage cases of USING and NATURAL with RIGHT and FULL joins (ADR 0012,
amendment 3, slice 4d).

The cases follow the "Tests" list of the slice 4d task: the merged name of a right join
(the right column, a REAL `1.0` against an INTEGER `1`) and of a full join (the coalesce,
which has no affinity in `WHERE`); its result name; `*`, `x.*` and qualified names;
`GROUP BY` and `ORDER BY`; chains of merges; `NATURAL RIGHT JOIN` and
`NATURAL FULL JOIN`; the coalesced left side of a later `USING`; and the prepare errors
`ambiguous reference to a in USING()`, also before the right join and for `NATURAL`,
`cannot join using column` and `ambiguous column name`. Native SQLite is the only source
of outcomes. The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE t(a INTEGER, b TEXT); CREATE TABLE r(a REAL, e TEXT); CREATE TABLE u(A INTEGER, c TEXT); "
          "CREATE TABLE w(a, f TEXT); "
          "INSERT INTO t VALUES(1, 'x'), (2, 'y'); INSERT INTO r VALUES(1.0, 'one'), (3.0, 'three'); "
          "INSERT INTO u VALUES(1, 'p'), (3, 'q'); INSERT INTO w VALUES(3, 'w3'), (4, 'w4');")
"""Four tables that share `a`: `r.a` is REAL, `u.a` is declared `A`, and `w.a` has no
declared type, so a coalesce can be compared with it without an affinity conversion."""

RIGHT = "R-15753-04279"
"""SQLite: a right join adds each unmatched right row, after the ON or USING filter."""
FULL = "R-18902-30764"
"""SQLite: a full join is a combination of a left and a right join."""
OMITTED = "R-57047-10461"
"""SQLite: the right column of each pair of a USING clause is omitted from the dataset."""
CONDITION = "R-54152-55276"
"""SQLite: for each pair of named columns, `lhs.X = rhs.X` must be true."""
NAMES = "R-48861-28451"
"""SQLite: the tables of FROM are joined into one dataset for the SELECT to operate on."""
MISSING = "R-49933-05137"
"""SQLite: each name of USING must exist in the datasets left and right of the join."""


def definitions() -> list[QueryCase]:
    """The coverage cases of USING and NATURAL with RIGHT and FULL joins."""
    case = QueryCase
    return [
        case("merged-right-column", TABLES, "SELECT a FROM t RIGHT JOIN r USING (a);", (RIGHT, OMITTED),
             ("using", "right")),
        case("merged-full-coalesce", TABLES, "SELECT a FROM t FULL JOIN r USING (a);", (FULL, OMITTED),
             ("using", "full")),
        case("merged-right-star", TABLES, "SELECT * FROM t RIGHT JOIN r USING (a);", (RIGHT, OMITTED),
             ("using", "right", "star")),
        case("merged-full-star", TABLES, "SELECT * FROM t FULL JOIN r USING (a);", (FULL, OMITTED),
             ("using", "full", "star")),
        case("merged-right-name", TABLES, "SELECT A FROM t RIGHT JOIN u USING (a);", (NAMES,),
             ("using", "right", "names")),
        case("merged-full-name", TABLES, "SELECT A FROM t FULL JOIN u USING (a);", (NAMES,),
             ("using", "full", "names")),
        case("merged-full-where-text", TABLES, "SELECT a FROM t FULL JOIN u USING (a) WHERE a = '3';", (FULL,),
             ("using", "full", "where", "affinity")),
        case("merged-full-where-number", TABLES, "SELECT a FROM t FULL JOIN u USING (a) WHERE a = 3;", (FULL,),
             ("using", "full", "where")),
        case("merged-full-group-by", TABLES,
             "SELECT a, count(*) FROM t FULL JOIN r USING (a) GROUP BY a ORDER BY 1;", (FULL,),
             ("using", "full", "group-by")),
        case("merged-right-qualified", TABLES, "SELECT t.a, r.a, a FROM t RIGHT JOIN r USING (a);", (NAMES,),
             ("using", "right", "qualified")),
        case("merged-full-source-star", TABLES, "SELECT r.*, t.* FROM t FULL JOIN r USING (a);", (NAMES,),
             ("using", "full", "star")),
        case("merged-right-source-star", TABLES, "SELECT t.*, r.* FROM t RIGHT JOIN r USING (a);", (NAMES,),
             ("using", "right", "star")),
        case("merged-chain-middle-star", TABLES, "SELECT r.* FROM t FULL JOIN r USING (a) FULL JOIN w USING (a);",
             (NAMES,), ("using", "full", "chain", "star")),
        case("merged-full-then-full", TABLES, "SELECT a FROM t FULL JOIN r USING (a) FULL JOIN w USING (a);",
             (FULL, CONDITION), ("using", "full", "chain")),
        case("merged-right-then-full", TABLES, "SELECT a FROM t RIGHT JOIN r USING (a) FULL JOIN w USING (a);",
             (RIGHT, FULL), ("using", "right", "full", "chain")),
        case("merged-full-then-right", TABLES, "SELECT a FROM t FULL JOIN r USING (a) RIGHT JOIN w USING (a);",
             (RIGHT, FULL), ("using", "right", "full", "chain")),
        case("merged-full-then-inner", TABLES, "SELECT * FROM t FULL JOIN r USING (a) JOIN w USING (a);",
             (FULL, CONDITION), ("using", "full", "chain")),
        case("merged-left-then-full", TABLES, "SELECT a FROM t LEFT JOIN r USING (a) FULL JOIN w USING (a);",
             (FULL,), ("using", "left", "full", "chain")),
        case("merged-right-then-using", TABLES, "SELECT * FROM t RIGHT JOIN u USING (a) JOIN w USING (a);",
             (RIGHT, CONDITION), ("using", "right", "chain")),
        case("merged-natural-right", TABLES, "SELECT * FROM t NATURAL RIGHT JOIN r;", (RIGHT, "R-04932-55942"),
             ("natural", "right")),
        case("merged-natural-full", TABLES, "SELECT * FROM t natural Full Join u;", (FULL, "R-04932-55942"),
             ("natural", "full")),
        case("merged-ambiguous-reference", TABLES, "SELECT * FROM t JOIN u ON t.b = u.c RIGHT JOIN w USING (a);",
             (NAMES,), ("using", "right", "prepare-error")),
        case("merged-ambiguous-reference-before-right", TABLES,
             "SELECT * FROM t JOIN u ON t.b = u.c JOIN w USING (a) RIGHT JOIN r ON r.e = w.f;", (NAMES,),
             ("using", "right", "prepare-error")),
        case("merged-ambiguous-reference-natural", TABLES, "SELECT * FROM t JOIN u ON t.b = u.c NATURAL FULL JOIN w;",
             (NAMES,), ("natural", "full", "prepare-error")),
        case("merged-missing-column", TABLES, "SELECT * FROM t RIGHT JOIN u USING (zz);", (MISSING,),
             ("using", "right", "prepare-error")),
        case("merged-ambiguous-third", TABLES, "SELECT a FROM t FULL JOIN u USING (a) JOIN w ON w.f = 'w3';",
             (NAMES,), ("using", "full", "prepare-error", "ambiguous")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `merged`."""
    return query_records(definitions() if cases is None else cases, part="merged")
