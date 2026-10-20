"""Authored coverage cases of `printf` and `format` (ADR 0015, slice 6).

The cases follow the "Tests" list of the slice 6 task: the integer, double, text and quoting
conversions, their flags, width and precision, `*`, missing arguments, the conversions that end
the output, NULL, and `printf` in writes. Native SQLite is the only source of outcomes. The
cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE p(k INTEGER PRIMARY KEY, i INTEGER, r REAL, t TEXT); "
          "INSERT INTO p VALUES(1, 42, 3.14159, 'abc'), (2, -7, -0.0, 'it''s'), (3, NULL, 1e300, NULL), "
          "(4, 9223372036854775807, 2.5e-7, 'été');")
"""One table with integers (one the largest), REALs (negative zero, large and small), text with a
quote and with two-byte characters, and NULL."""

FORMAT = "R-32560-14372"
"""SQLite: the format(FORMAT,...) SQL function works like the sqlite3_mprintf() C-language
function and the printf() function from the standard C library."""
ALIAS = "R-64900-53159"
"""SQLite: the printf() SQL function is an alias for the format() SQL function."""


def definitions() -> list[QueryCase]:
    """The coverage cases of slice 6 of ADR 0015."""
    case = QueryCase
    return [
        case("printf-integers", TABLES, "SELECT k, printf('%d|%5d|%-5d|%05d|%+d|% d|%,d|%u|%x|%#X|%o|%#o|%r|%p', "
             "i, i, i, i, i, i, i, i, i, i, i, i, i, i) FROM p ORDER BY k;", (FORMAT,), ("functions", "printf")),
        case("printf-doubles", TABLES, "SELECT k, printf('%f|%.2f|%10.3e|%E|%g|%#g|%!g|%G|%-12.4f|%010.2f|%+.1e|%,.2f', "
             "r, r, r, r, r, r, r, r, r, r, r, r) FROM p ORDER BY k;", (FORMAT,), ("functions", "printf")),
        case("printf-text", TABLES, "SELECT k, format('%s|%10s|%-6s|%.2s|%!.2s|%!6s|%q|%Q|%w|%c|%.3c|%z', "
             "t, t, t, t, t, t, t, t, t, t, t, t) FROM p ORDER BY k;", (FORMAT, ALIAS), ("functions", "format")),
        case("printf-special", TABLES, "SELECT printf('%*d|%-*d|%.*f|%*.*s', 6, 42, -6, 42, 2, 3.14159, 8, 3, 'abcdef'), "
             "printf('%d %d %s'), printf('100%%'), printf('a%n%Tb', 1), printf('x%yz', 1), printf('%'), "
             "printf(NULL, 1), printf('%lld %ld', 5, 6), printf('%f|%e|%010f', 1e308 * 10, -1e308 * 10, 1e308 * 10), "
             "printf('%#q|%#Q|%#Q', 'a\\b', 'x', NULL), printf('%.0f|%.1f|%.1f', 2.5, 0.25, 0.35), "
             "printf(5), format('%s', 2.5e-7);", (FORMAT,), ("functions", "printf")),
        case("printf-in-writes", TABLES, "UPDATE p SET t = printf('%03d-%s', k, t) WHERE k = 1 OR k = 2; "
             "INSERT INTO p(k, t) VALUES (5, printf('%.3f', 2.0 / 3)); SELECT k, t FROM p ORDER BY k;",
             (FORMAT,), ("functions", "printf", "update")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `printf`."""
    return query_records(definitions() if cases is None else cases, part="printf")
