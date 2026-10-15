"""Authored coverage cases of joins (ADR 0012, amendment 2, slice 4).

The cases follow the amendment's "Testing" list: each join form; inner joins with no,
one and several matches per row; left joins with unmatched left rows, a right-table
condition in ON and the same condition in WHERE; three tables; a self-join with aliases;
qualified and unqualified names, `*` and `x.*`; aggregates and GROUP BY over a join;
ORDER BY a qualified name; the prepare errors of names; and `x.*` in RETURNING, which
SQLite refuses before it resolves the other RETURNING columns. Native SQLite is the only
source of outcomes. The cases use `conformance.authored_queries.QueryCase` and its
recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE t(a INTEGER, b TEXT); CREATE TABLE u(a INTEGER, c TEXT); CREATE TABLE v(a INTEGER, d TEXT); "
          "INSERT INTO t VALUES(1, 'x'), (2, 'y'), (3, 'z'); "
          "INSERT INTO u VALUES(1, 'p'), (1, 'q'), (3, 'r'), (4, 's'); INSERT INTO v VALUES(1, 'm'), (3, 'n');")
"""Three tables that share the column name `a`: in `t`, row 1 matches two rows of `u`, row 2
none and row 3 one; `v` matches rows 1 and 3."""

PRODUCT = "R-44414-54710"
"""SQLite: the cartesian product has a row for each combination of a left and a right row."""
ON = "R-38465-03616"
"""SQLite: an ON condition keeps the rows of the product for which it is true."""
LEFT = "R-24610-05866"
"""SQLite: a left join adds each unmatched left row with NULL in the right columns."""
NAMES = "R-48861-28451"
"""SQLite: the tables of FROM are joined into one dataset for the SELECT to operate on."""


def definitions() -> list[QueryCase]:
    """The coverage cases of joins."""
    case = QueryCase
    return [
        case("join-comma-product", TABLES, "SELECT t.a, u.a FROM t, u;", (PRODUCT,), ("join", "comma")),
        case("join-cross", TABLES, "SELECT * FROM t CROSS JOIN v;", ("R-25071-21202",), ("join", "cross")),
        case("join-inner-on", TABLES, "SELECT t.b, u.c FROM t JOIN u ON t.a = u.a;", (ON,), ("join", "inner", "on")),
        case("join-inner-keyword-where", TABLES,
             "SELECT t.b, u.c FROM t INNER JOIN u ON t.a = u.a WHERE u.c <> 'q';", ("R-46256-57243",),
             ("join", "inner", "where")),
        case("join-left-unmatched", TABLES, "SELECT t.b, u.c FROM t LEFT JOIN u ON t.a = u.a;", (LEFT,),
             ("join", "left")),
        case("join-left-condition-in-on", TABLES,
             "SELECT t.b, u.c FROM t LEFT JOIN u ON t.a = u.a AND u.c = 'p';", (LEFT,), ("join", "left", "on")),
        case("join-left-condition-in-where", TABLES,
             "SELECT t.b, u.c FROM t LEFT JOIN u ON t.a = u.a WHERE u.c = 'p';", (LEFT,), ("join", "left", "where")),
        case("join-left-outer", TABLES, "SELECT * FROM t left Outer join v ON t.a = v.a;", (LEFT,),
             ("join", "left", "outer")),
        case("join-three-tables", TABLES,
             "SELECT t.b, u.c, v.d FROM t JOIN u ON t.a = u.a JOIN v ON u.a = v.a;", ("R-28760-53843",),
             ("join", "three")),
        case("join-self-aliases", TABLES, "SELECT x.a, y.a FROM t AS x JOIN t y ON x.a < y.a;", (NAMES,),
             ("join", "alias", "self")),
        case("join-unqualified-names", TABLES, "SELECT b, c FROM t JOIN u ON t.a = u.a;", (NAMES,),
             ("join", "names")),
        case("join-star-and-source-star", TABLES, "SELECT *, u.* FROM t JOIN u ON t.a = u.a;",
             ("R-59089-25828",), ("join", "star")),
        case("join-aggregate-group-by", TABLES,
             "SELECT t.b, count(*), max(u.c) FROM t JOIN u ON t.a = u.a GROUP BY t.b ORDER BY 1;", (NAMES,),
             ("join", "aggregate")),
        case("join-left-count-padded", TABLES,
             "SELECT t.b, count(u.c) FROM t LEFT JOIN u ON t.a = u.a GROUP BY t.b;", (LEFT,),
             ("join", "left", "aggregate")),
        case("join-order-by-qualified", TABLES, "SELECT t.a, u.c FROM t JOIN u ON t.a = u.a ORDER BY u.c DESC LIMIT 2;",
             (NAMES,), ("join", "order-by")),
        case("join-ambiguous-column", TABLES, "SELECT a FROM t JOIN u ON t.a = u.a;", (NAMES,),
             ("join", "prepare-error", "ambiguous")),
        case("join-ambiguous-in-on", TABLES, "SELECT * FROM t JOIN u ON a = 1;", (NAMES,),
             ("join", "prepare-error", "ambiguous", "on")),
        case("join-alias-hides-table", TABLES, "SELECT t.a FROM t AS x;", (NAMES,), ("join", "prepare-error", "alias")),
        case("join-no-such-source-column", TABLES, "SELECT zz.a FROM t;", (NAMES,), ("join", "prepare-error")),
        case("join-no-such-source-star", TABLES, "SELECT zz.* FROM t;", (NAMES,), ("join", "prepare-error", "star")),
        case("join-returning-source-star", TABLES, "DELETE FROM t WHERE a = 2 RETURNING zz, t.*;",
             ("R-46605-62546",), ("returning", "prepare-error", "star")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `joins`."""
    return query_records(definitions() if cases is None else cases, part="joins")
