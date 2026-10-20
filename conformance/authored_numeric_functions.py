"""Authored coverage cases of the exact numeric functions (ADR 0015, slice 2).

The cases follow the "Tests" list of the slice 2 task: `round` with and without digits,
`floor`, `ceil`, `ceiling` and `trunc` of integers, REALs, numeric text and other values,
`sqrt`, `pi`, `degrees`, `radians` and `mod`, with the sign of zero, large values and the
NULL results. Native SQLite is the only source of outcomes. SQLite's documentation of the
math functions (`lang_mathfunc.html`) has no requirement marks, so those cases name the
requirement of the result columns of a simple SELECT. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE n(k INTEGER PRIMARY KEY, i INTEGER, r REAL, t TEXT, b BLOB); "
          "INSERT INTO n VALUES(1, -7, 2.5, '3.7', x'01'), (2, 9, -2.5, 'x', NULL), "
          "(3, NULL, -0.4, '-6', x''), (4, 4503599627370497, 1e20, ' 8 ', x'02'), "
          "(5, 0, -0.5, '1e400', NULL);")
"""One table with integers (one beyond 2^52), REALs around the rounding cases, numeric and
other text, and BLOBs."""

ROUND = "R-10715-11594"
"""SQLite: round(X,Y) returns X rounded to Y digits to the right of the decimal point."""
RESULTS = "R-08669-22397"
"""SQLite: a simple SELECT returns one column for each result expression. The math functions
have no requirement marks of their own."""


def definitions() -> list[QueryCase]:
    """The coverage cases of slice 2 of ADR 0015."""
    case = QueryCase
    return [
        case("numeric-round", TABLES, "SELECT round(i), round(r), round(t), round(b), round(r, 1), "
             "round(i, 2), typeof(round(i)) FROM n;", (ROUND,), ("functions", "round")),
        case("numeric-round-digits", TABLES, "SELECT round(1.005, 2), round(-0.001, 2), round(2.567, 1), "
             "round(2.5, NULL), round(NULL, 1), round(123.456, -1), round(1.5, 40), round(1e300, 3);",
             (ROUND,), ("functions", "round")),
        case("numeric-round-sign", TABLES, "SELECT round(-0.4), round(-0.001, 2), trunc(-0.5), ceil(-0.5), "
             "mod(-6, 3), floor(-0.0);", (ROUND, RESULTS), ("functions", "round", "zero-sign")),
        case("numeric-floor-ceil-trunc", TABLES, "SELECT floor(i), floor(r), floor(t), floor(b), ceil(r), "
             "ceiling(t), trunc(r), trunc(t), typeof(floor(i)) FROM n;", (RESULTS,),
             ("functions", "floor", "ceil", "trunc")),
        case("numeric-rounding-sign", TABLES, "SELECT quote(trunc(-0.5)), quote(ceil(-0.5)), "
             "quote(floor(-0.0)), floor(2.5e15), ceil(-4503599627370495.5), trunc(1e300);", (RESULTS,),
             ("functions", "floor", "ceil", "trunc", "zero-sign")),
        case("numeric-sqrt-pi", TABLES, "SELECT sqrt(i), sqrt(r), sqrt(t), sqrt(b), sqrt(2), pi(), "
             "sqrt(-1) FROM n;", (RESULTS,), ("functions", "sqrt", "pi")),
        case("numeric-degrees-radians", TABLES, "SELECT degrees(pi()), radians(180), degrees(r), radians(i), "
             "degrees(t), radians(NULL) FROM n;", (RESULTS,), ("functions", "degrees", "radians")),
        case("numeric-mod", TABLES, "SELECT mod(i, 3), mod(r, 2), mod(t, 2), mod(i, 0), mod(b, 2), "
             "mod(7, 3), mod(-7, 3), mod(7.5, 2), mod(1e300, 7), mod(5, 1e-300) FROM n;", (RESULTS,),
             ("functions", "mod")),
        case("numeric-in-writes", TABLES, "UPDATE n SET r = round(r * 3, 1), i = floor(r) WHERE k < 3; "
             "SELECT k, i, r FROM n;", (ROUND,), ("functions", "update")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `numeric-functions`."""
    return query_records(definitions() if cases is None else cases, part="numeric-functions")
