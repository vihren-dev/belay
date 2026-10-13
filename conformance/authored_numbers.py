"""Authored coverage cases of numbers in queries (ADR 0012, slice 2, "Tests" of the task).

Each rule has a case where it applies and the boundary values that the task lists:
overflow at both 64-bit limits, division and remainder by zero and by -1, a NaN
result, REAL remainder, TEXT operands, REAL literals that SQLite converts without
correct rounding, CAST of each storage class to each affinity, COALESCE and its
argument count, and SUM and AVG with integers, REAL values, TEXT, NULL, an overflow,
an overflow that a REAL input clears, and no rows. Native SQLite is the only source of
outcomes. The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

MIXED = ("CREATE TABLE t(k, v TEXT, n INTEGER, r REAL); INSERT INTO t VALUES(NULL, 'a', 1, 1.5), "
         "(2, '7', 2, -2.5), ('1.5', '1e3', NULL, 0.1), ('x', ' 7 ', 3, NULL), "
         "(X'01', 'abc', 9223372036854775807, 1e308), (2.0, NULL, -9223372036854775808, 2.0);")
"""Each storage class in `k`, numeric and other text in `v`, both 64-bit limits in `n`,
and a large REAL in `r`."""
EDGE = ("CREATE TABLE e(a INTEGER, b INTEGER); INSERT INTO e VALUES(9223372036854775807, 1), "
        "(-9223372036854775808, -1), (-9223372036854775808, 2), (7, 0), (-7, 2), (7, -1);")
"""Operand pairs at the 64-bit limits, with a zero and a -1 divisor."""
SUMS = ("CREATE TABLE s(g, x); INSERT INTO s VALUES(1, 9223372036854775807), (1, 1), "
        "(2, 9223372036854775807), (2, 1), (2, 0.5), (3, NULL), (4, '7'), (4, 'abc'), (5, 1.5), (5, 2), "
        "(6, 1e16), (6, 1.0), (6, 1.0);")
"""Groups of SUM inputs: an overflow, an overflow and then a REAL, only NULL, TEXT,
REAL and integer, and a sum that needs the compensated summation."""
ONE = "CREATE TABLE o(x); INSERT INTO o VALUES(1);"
"""A table with one row, for expressions of literals."""


def definitions() -> list[QueryCase]:
    """The coverage cases of numbers in queries."""
    case = QueryCase
    return [
        case("add-subtract-multiply-limits", EDGE, "SELECT a, b, a + b, a - b, a * b FROM e;", ("R-12720-41494",),
             ("arithmetic", "integer-overflow")),
        case("divide-remainder-limits", EDGE, "SELECT a, b, a / b, a % b FROM e;", ("R-53431-59159",),
             ("arithmetic", "division-by-zero", "integer-overflow")),
        case("real-arithmetic", MIXED, "SELECT r, r + 1, r * r, r / 0, r % 2, -r FROM t;", ("R-18364-25640",),
             ("arithmetic", "real", "division-by-zero")),
        case("nan-is-null", MIXED, "SELECT r, r * 1e308 - r * 1e308 FROM t;", ("R-12720-41494",), ("arithmetic", "nan")),
        case("text-operands", MIXED, "SELECT v, v + 0, v * 2, v / 2, k - 1 FROM t;", ("R-12720-41494", "R-27875-27272"),
             ("arithmetic", "text-conversion")),
        case("unary-operators", MIXED, "SELECT n, -n, +n, -(-n), -r FROM t;", ("R-53670-03373",),
             ("arithmetic", "unary", "integer-overflow")),
        case("unary-plus-has-no-affinity", MIXED, "SELECT n FROM t WHERE +v = 7;", ("R-08041-13327",),
             ("affinity", "unary")),
        case("real-literals", ONE, "SELECT 1.5, -2.5e3, .5, 1e308 * 10, 9223372036854775808, -9223372036854775809, "
             "0.1 + 0.2 FROM o;", ("R-31536-32008",), ("literal", "real")),
        case("literals-not-correctly-rounded", ONE, "SELECT 2.6018159083016613186e-270, 2.2250738585072011e-308 FROM o;",
             ("R-31536-32008",), ("literal", "real", "rounding")),
        case("hex-literals", ONE, "SELECT 0x7FFFFFFFFFFFFFFF, -0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF FROM o;",
             ("R-31536-32008",), ("literal", "hex")),
        case("hex-literal-too-big-negated", ONE, "SELECT -0x8000000000000000 FROM o;", ("R-31536-32008",),
             ("literal", "hex", "prepare-error")),
        case("cast-integer", MIXED, "SELECT CAST(k AS INTEGER), CAST(v AS INTEGER), CAST(r AS INTEGER), "
             "CAST(n AS INTEGER) FROM t;", ("R-02752-50091", "R-47612-45842", "R-28651-34639"), ("cast",)),
        case("cast-real", MIXED, "SELECT CAST(k AS REAL), CAST(v AS REAL), CAST(n AS REAL) FROM t;", ("R-54898-34554",),
             ("cast",)),
        case("cast-numeric", MIXED, "SELECT CAST(k AS NUMERIC), CAST(v AS NUMERIC), CAST(r AS NUMERIC), "
             "CAST(4.0 AS NUMERIC), CAST('4.0' AS NUMERIC) FROM t;", ("R-07327-11967",), ("cast",)),
        case("cast-text-and-blob", MIXED, "SELECT CAST(r AS TEXT), CAST(n AS TEXT), CAST(k AS TEXT), CAST(n AS BLOB) FROM t;",
             ("R-32434-09092",), ("cast", "real-text")),
        case("cast-type-names", MIXED, "SELECT CAST(v AS VARCHAR(10)), CAST(v AS FLOATING POINT), CAST(v AS whatever), "
             "CAST(n AS int) FROM t;", ("R-29946-11104",), ("cast", "affinity")),
        case("cast-null", ONE, "SELECT CAST(NULL AS INTEGER), CAST(NULL AS TEXT) FROM o;", ("R-32434-09092",),
             ("cast", "null")),
        case("cast-compares-with-its-affinity", MIXED, "SELECT n FROM t WHERE CAST(v AS INTEGER) = 7;",
             ("R-56101-50212",), ("cast", "affinity")),
        case("real-to-text-digits", ONE, "SELECT CAST(0.1 + 0.2 AS TEXT), CAST(1e15 AS TEXT), CAST(1e14 AS TEXT), "
             "CAST(123456789012345.6 AS TEXT), CAST(1e-5 AS TEXT), CAST(1.7976931348623157e308 AS TEXT) FROM o;",
             ("R-32434-09092",), ("cast", "real-text")),
        case("coalesce", MIXED, "SELECT coalesce(k, v, n), coalesce(NULL, r), COALESCE(NULL, NULL, 3) FROM t;",
             ("R-22655-13879",), ("coalesce", "null")),
        case("coalesce-one-argument", MIXED, "SELECT coalesce(n) FROM t;", ("R-22655-13879",),
             ("coalesce", "prepare-error")),
        case("count-two-arguments", MIXED, "SELECT count(n, r) FROM t;", ("R-22655-13879",), ("count", "prepare-error")),
        case("sum-avg-kinds", SUMS, "SELECT g, sum(x), avg(x) FROM s WHERE g > 2 GROUP BY g;",
             ("R-19660-56479", "R-33611-59266", "R-44223-43966", "R-17177-10067"), ("sum", "avg", "group-by")),
        case("sum-overflow", SUMS, "SELECT sum(x) FROM s WHERE g = 1;", ("R-08904-24719",), ("sum", "integer-overflow")),
        case("sum-overflow-then-real", SUMS, "SELECT sum(x), avg(x) FROM s WHERE g = 2;", ("R-08904-24719",),
             ("sum", "avg", "integer-overflow")),
        case("avg-overflow-succeeds", SUMS, "SELECT avg(x) FROM s WHERE g = 1;", ("R-20409-33051",),
             ("avg", "integer-overflow")),
        case("sum-no-rows", SUMS, "SELECT sum(x), avg(x), count(x) FROM s WHERE g > 9;", ("R-44223-43966",),
             ("sum", "avg", "empty-result")),
        case("sum-compensated", SUMS, "SELECT sum(x) FROM s WHERE g = 6;", ("R-33611-59266",), ("sum", "real")),
        case("arithmetic-in-where-and-order", MIXED, "SELECT n, n * 2 AS d FROM t WHERE n % 2 = 1 ORDER BY d DESC;",
             ("R-60775-64916",), ("arithmetic", "where", "order-by")),
        case("arithmetic-condition", MIXED, "SELECT n FROM t WHERE n - 1;", ("R-60775-64916",), ("arithmetic", "where")),
        case("integer-real-equality", ONE, "SELECT 1 = 1.0, 9007199254740993 = 9007199254740992.0, 0.1 + 0.2 = 0.3 FROM o;",
             ("R-12881-55998",), ("comparison", "real")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `numbers`."""
    return query_records(definitions() if cases is None else cases, part="numbers")
