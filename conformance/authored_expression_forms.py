"""Authored coverage cases of the expression forms IN, BETWEEN, CASE and || (ADR 0018, slice 2).

The cases follow the "Tests" list of the slice 2 task: each form in a result column, in `WHERE`
and in a write; the affinity and collation rules of the `IN` list, of `BETWEEN` and of `CASE`
with a base; the NULL matrix of the `IN` list; and the text of integers, REAL values and BLOBs
in `||`. Native SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE t(i INTEGER, s TEXT, n TEXT COLLATE NOCASE, b); "
          "INSERT INTO t VALUES(1, '1', 'A', '1'), (2, '2', 'b', NULL), (NULL, 'x', NULL, x'41'); "
          "CREATE TABLE w(k INTEGER PRIMARY KEY, v);")
"""A table with an INTEGER, a TEXT, a NOCASE and an untyped column, whose rows hold a NULL in
each; and an empty table that writes fill."""

IN_LIST = "R-15810-56691"
"""SQLite: IN and NOT IN take an expression on the left and a list of values or a subquery."""
IN_NO_AFFINITY = "R-18219-48316"
"""SQLite: the values to the right of IN have no affinity, even if they are columns."""
IN_MATRIX = "R-50221-42915"
"""SQLite: the result of IN and NOT IN follows the matrix of NULL, empty and found operands."""
EMPTY_LIST = "R-64309-54027"
"""SQLite: the list on the right of IN may be empty."""
BETWEEN = "R-40079-54503"
"""SQLite: x BETWEEN y AND z is x >= y AND x <= z, with x evaluated once."""
BETWEEN_AFFINITY = "R-46475-65007"
"""SQLite: BETWEEN is two comparisons, even if different affinities apply to x in each."""
CASE_BASE = "R-11479-62774"
"""SQLite: the base and a WHEN value compare with the collation, affinity and NULL rules of =."""
CASE_NULL_BASE = "R-37304-39405"
"""SQLite: a NULL base gives the ELSE value, or NULL without ELSE."""
CASE_WHEN = "R-30638-59954"
"""SQLite: without a base, each WHEN value is a boolean, from left to right."""
CASE_NO_ELSE = "R-14168-07579"
"""SQLite: without ELSE and without a true WHEN, the result is NULL."""
CONCAT = "R-44409-62641"
"""SQLite: || joins the strings of its operands."""


def definitions() -> list[QueryCase]:
    """The coverage cases of the expression forms."""
    case = QueryCase
    return [
        case("form-in-list-affinity", TABLES,
             "SELECT i, i IN ('1', 'x'), i IN (s, 9), '1' IN (i, 'z'), s IN (1, 2), b IN (1, 2) FROM t ORDER BY i;",
             (IN_LIST, IN_NO_AFFINITY), ("in-list", "affinity")),
        case("form-in-list-collation", TABLES,
             "SELECT n, n IN ('a', 'z'), 'a' IN (n, 'z'), n IN ('a' COLLATE BINARY, 'z'), "
             "n IN ('a' COLLATE BINARY) FROM t ORDER BY n;",
             (IN_LIST,), ("in-list", "collation")),
        case("form-in-list-nulls", TABLES,
             "SELECT i, i IN (1, NULL), i NOT IN (1, NULL), i IN (), i NOT IN (), NULL IN (), i IN (b, 7) FROM t ORDER BY i;",
             (IN_MATRIX, EMPTY_LIST), ("in-list", "null")),
        case("form-in-list-where", TABLES,
             "SELECT s FROM t WHERE i NOT IN (2, 3) ORDER BY s;", (IN_LIST, IN_MATRIX), ("in-list", "where")),
        case("form-between", TABLES,
             "SELECT i, i BETWEEN '0' AND '1', s BETWEEN 0 AND 2, i BETWEEN NULL AND 1, 3 BETWEEN NULL AND 2, "
             "n BETWEEN 'a' AND 'a', i NOT BETWEEN 1 AND 1 FROM t ORDER BY i;",
             (BETWEEN, BETWEEN_AFFINITY), ("between",)),
        case("form-case-base", TABLES,
             "SELECT i, CASE i WHEN '1' THEN 'one' WHEN 2 THEN 'two' ELSE 'other' END, "
             "CASE n WHEN 'a' THEN 'A' END, CASE 'B' WHEN n THEN 'n' ELSE '-' END, "
             "CASE i WHEN NULL THEN 'null' ELSE 'not' END FROM t ORDER BY i;",
             (CASE_BASE, CASE_NULL_BASE, CASE_NO_ELSE), ("case", "base")),
        case("form-case-when", TABLES,
             "SELECT i, CASE WHEN i > 1 THEN 'big' WHEN i THEN 'one' END, CASE WHEN 'x' THEN 1 WHEN '2x' THEN 2 "
             "ELSE 3 END FROM t ORDER BY i;",
             (CASE_WHEN, CASE_NO_ELSE), ("case", "when")),
        case("form-concat", TABLES,
             "SELECT i, i || s, s || n, i || b, 1.5 || 'a', 1e300 || '', 100.0 || '', -0.0 || '', "
             "typeof(i || i) FROM t ORDER BY i;",
             (CONCAT,), ("concat",)),
        case("form-writes", TABLES,
             "INSERT INTO w(v) VALUES (CASE WHEN 1 THEN 'a' || 'b' END), "
             "(2 BETWEEN 1 AND 3); UPDATE w SET v = v || '!' WHERE k IN (1, 3); DELETE FROM w WHERE v NOT IN ('ab!'); "
             "SELECT k, v FROM w ORDER BY k;",
             (CONCAT, BETWEEN, IN_LIST), ("writes",)),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `expression-forms`."""
    return query_records(definitions() if cases is None else cases, part="expression-forms")
