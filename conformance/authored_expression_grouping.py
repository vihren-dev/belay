"""Native inputs for grouping terms that are expressions (ADR 0030, slice 3).

The cases follow "Grouping: SQLite" of the ADR: a term is any expression that the model resolves
in `WHERE`; an integer, also under parentheses, unary plus and minus or `COLLATE`, names a
result column, and every other literal is a constant; the term compares without affinity under its collation,
which is an explicit `COLLATE`, else the column's through unary plus and `CAST`, else `BINARY`;
an aggregate in a term and a term out of range are SQLite's errors; a key that fails for a kept
row fails the statement, and the model says only that such a key may fail (ADR 0030, D4), so the
corpus has the failing key without kept rows only. A query without `ORDER BY` is compared without order. SQLite supplies
every outcome through the query recorder.
"""

from conformance.authored_clock import SETUP_CLOCK, profile as clock_profile
from conformance.authored_queries import QueryCase
from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.native_record import record_sql

KEYS = ("CREATE TABLE g(a, b, c TEXT COLLATE NOCASE, n); "
        "INSERT INTO g VALUES(1.0, 'x', 'a', 1), (1, 'Y', 'A', 3), ('1', 'y', 'b', 2), (x'31', 'X ', 'B', 5), "
        "(NULL, 'x', 'a', 4), (NULL, 'z', 'c', 6);")
"""Keys of each storage class: `1.0`, `1`, `'1'` and `x'31'` are one value after `+0` and three
values as written, because `1.0` and `1` are equal; two NULLs; `c` with NOCASE pairs; `b` with case and a
trailing space."""
DAYS = ("CREATE TABLE d(x INTEGER, n); "
        "INSERT INTO d VALUES(1735603200, 1), (1735606800, 2), (1735689600, 3), (1735693200, 4);")
"""Unix times: two on 2024-12-31 and two on 2025-01-01."""

GROUP_TERM = "R-25883-55063"
"""SQLite: each GROUP BY expression is evaluated for each row, and rows with equal values are one group."""
NO_AFFINITY = "R-40564-64233"
"""SQLite: no affinity is applied to GROUP BY values before they are compared."""
GROUP_COLLATION = "R-10470-30318"
"""SQLite: GROUP BY values compare under the collation of the expression."""
AGGREGATE_TERM = "R-63573-50730"
"""SQLite: a GROUP BY expression may not be an aggregate."""
ARBITRARY_ROW = "R-62913-19830"
"""SQLite: a non-aggregate expression of an aggregate query is evaluated against a single row of the group."""


def definitions() -> list[QueryCase]:
    """The cases: storage classes and `+0`, NULL keys, the collation of a term, aliases and
    shadowing, the numbers of a term, aggregate terms, a failing key without kept rows, the values of a group with
    an expression term, and grouped result expressions."""
    def case(name: str, sql: str, requirements: tuple[str, ...], *features: str, setup: str = KEYS) -> QueryCase:
        """Give a case its name prefix and the group-by feature."""
        return QueryCase("expression-grouping-" + name, setup, sql, requirements, ("group-by", *features))

    return [
        case("plus-zero", "SELECT count(*) AS k FROM g GROUP BY a+0;", (GROUP_TERM, NO_AFFINITY), "storage-class"),
        case("plus-zero-value", "SELECT a+0, count(*) FROM g GROUP BY a+0;", (GROUP_TERM, ARBITRARY_ROW),
             "storage-class"),
        case("typeof", "SELECT typeof(a), count(*) FROM g GROUP BY typeof(a);", (GROUP_TERM,), "storage-class"),
        case("null-test", "SELECT a IS NULL, count(*) FROM g GROUP BY a IS NULL;", (GROUP_TERM,), "null"),
        case("plus-column", "SELECT count(*) AS k FROM g GROUP BY +c;", (GROUP_COLLATION,), "collation"),
        case("cast-column", "SELECT count(*) AS k FROM g GROUP BY CAST(c AS TEXT);", (GROUP_COLLATION,), "collation"),
        case("concatenation", "SELECT count(*) AS k FROM g GROUP BY c || '';", (GROUP_COLLATION,), "collation"),
        case("function", "SELECT count(*) AS k FROM g GROUP BY rtrim(c);", (GROUP_COLLATION,), "collation"),
        case("collate-expression", "SELECT count(*) AS k FROM g GROUP BY (c || '') COLLATE NOCASE;",
             (GROUP_COLLATION,), "collation"),
        case("collate-rtrim", "SELECT count(*) AS k FROM g GROUP BY lower(b) COLLATE RTRIM;", (GROUP_COLLATION,),
             "collation"),
        case("collate-twice", "SELECT count(*) AS k FROM g GROUP BY c COLLATE NOCASE COLLATE BINARY;",
             (GROUP_COLLATION,), "collation"),
        case("alias", "SELECT lower(b) AS k, count(*) FROM g GROUP BY k;", (GROUP_TERM,), "alias"),
        case("alias-shadowed", "SELECT a+0 AS a, count(*) FROM g GROUP BY a;", (GROUP_TERM,), "alias"),
        case("number-in-parentheses", "SELECT b, count(*) FROM g GROUP BY (1);", (GROUP_TERM,), "number"),
        case("number-with-plus", "SELECT b, count(*) FROM g GROUP BY +1;", (GROUP_TERM,), "number"),
        case("number-hexadecimal", "SELECT b, count(*) FROM g GROUP BY 0x1;", (GROUP_TERM,), "number"),
        case("number-negated-twice", "SELECT b, count(*) FROM g GROUP BY - -1;", (GROUP_TERM,), "number"),
        case("number-negative", "SELECT b, count(*) FROM g GROUP BY -1;", (GROUP_TERM,), "number", "prepare-error"),
        case("number-under-collate", "SELECT c || '' AS k, max(n) FROM g WHERE c IS NOT NULL GROUP BY 1 COLLATE NOCASE;",
             (GROUP_COLLATION, ARBITRARY_ROW), "number", "collation"),
        case("alias-under-collate", "SELECT c || '' AS k, max(n) FROM g GROUP BY k COLLATE NOCASE;",
             (GROUP_COLLATION, ARBITRARY_ROW), "alias", "collation"),
        case("alias-under-collate-associated", "SELECT c || '' AS k, (c || '') COLLATE NOCASE AS again, max(n) FROM g "
             "GROUP BY k COLLATE NOCASE;", (GROUP_COLLATION, ARBITRARY_ROW), "alias", "collation", "association"),
        case("number-real", "SELECT count(*) AS k FROM g GROUP BY 1.0;", (GROUP_TERM,), "number"),
        case("number-text", "SELECT count(*) AS k FROM g GROUP BY '1';", (GROUP_TERM,), "number"),
        case("number-expression", "SELECT count(*) AS k FROM g GROUP BY 1+0;", (GROUP_TERM,), "number"),
        case("aggregate-inside", "SELECT count(*) AS k FROM g GROUP BY max(n)+1;", (AGGREGATE_TERM,),
             "prepare-error"),
        case("aggregate-alias", "SELECT b, max(n) AS m FROM g GROUP BY m;", (AGGREGATE_TERM,), "prepare-error"),
        case("aggregate-by-negation", "SELECT count(*) AS k FROM g GROUP BY - -1;", (AGGREGATE_TERM,),
             "prepare-error"),
        case("failing-key-no-row", "SELECT count(*) AS k FROM g WHERE 0 GROUP BY abs(-9223372036854775808 + n - n);",
             (GROUP_TERM,), "failure"),
        case("max-row", "SELECT a+0, (a+0)*1 AS again, max(n) FROM g WHERE a IS NOT NULL GROUP BY a+0;",
             (ARBITRARY_ROW,), "max"),
        case("written-twice", "SELECT a+0, a+0 AS again, max(n) FROM g WHERE a IS NOT NULL GROUP BY a+0;",
             (ARBITRARY_ROW,), "max", "association"),
        case("grouped-expression", "SELECT lower(b) || '!' AS k, count(*) FROM g GROUP BY lower(b);", (GROUP_TERM,),
             "grouped"),
        case("grouped-name-case", "SELECT LOWER(g.b) AS k, count(*) FROM g GROUP BY lower(B);", (GROUP_TERM,),
             "grouped"),
        case("parameter-free-call", "SELECT count(*) AS k FROM g GROUP BY length(b);", (GROUP_TERM,), "function"),
    ]


def date_cases() -> list[QueryCase]:
    """The cases whose term reads the clock: `date` of a column counts as a read of the clock."""
    return [QueryCase("expression-grouping-date", DAYS,
                      "SELECT date(x, 'unixepoch') AS day, sum(n) FROM d GROUP BY date(x, 'unixepoch');",
                      (GROUP_TERM,), ("group-by", "date"))]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 7 record: the cases of {definitions} under SQLite's
    default measured profile, and the date cases under the controlled clock."""
    selected = definitions() if cases is None else cases
    defaults = profile(())
    plain = [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                           profile=defaults, run_on=True, counters=True),
              "part": "expression-grouping", "features": list(case.features)}
             for case in selected]
    clocked = [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                             profile=clock_profile(), setup_clock=SETUP_CLOCK, clock_values=[SETUP_CLOCK],
                             run_on=True, counters=True),
                "part": "expression-grouping", "features": list(case.features)}
               for case in (date_cases() if cases is None else [])]
    return plain + clocked
