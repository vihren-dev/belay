"""Authored coverage cases of the function catalog, the text and type functions, and `LIKE`
and `GLOB` (ADR 0015, slice 1).

The cases follow the "Tests" list of the slice 1 task: SQLite's prepare errors of calls
(`no such function`, the number of arguments, and the errors of the arguments first); each
function of the slice with text, BLOB, numeric and NULL arguments; the run-time failures
(`abs` of the smallest integer, an `ESCAPE` of two characters); and calls in WHERE, ORDER
BY, VALUES and UPDATE. Native SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE v(k INTEGER PRIMARY KEY, i INTEGER, r REAL, t TEXT, b BLOB, n TEXT COLLATE NOCASE); "
          "INSERT INTO v VALUES(1, -7, 12.5, 'héllo', x'0102', 'Abc'), (2, 0, -0.5, 'a_c', x'', 'abc'), "
          "(3, NULL, NULL, NULL, NULL, NULL), (4, 9223372036854775807, 1e300, '-3', x'61', 'B');")
"""One table with an integer, a REAL, a text, a BLOB and a NOCASE column, and a row of NULLs."""

TYPEOF = "R-62084-05956"
"""SQLite: typeof(X) returns "null", "integer", "real", "text" or "blob"."""
LENGTH = "R-51887-27452"
"""SQLite: for a string X, length(X) returns the number of code points before the first NUL."""
OCTET_LENGTH = "R-01211-30624"
"""SQLite: octet_length(X) returns the number of bytes in the encoding of X."""
ABS = "R-23979-26855"
"""SQLite: abs(X) returns the absolute value of X."""
ABS_OVERFLOW = "R-46841-39732"
"""SQLite: abs(-9223372036854775808) throws an integer overflow error."""
SIGN = "R-03595-19994"
"""SQLite: sign(X) returns -1, 0 or +1 for a negative, zero or positive number."""
SIGN_OTHER = "R-61228-42590"
"""SQLite: sign(X) of NULL, or of text or a BLOB that is no number, is NULL."""
ZEROBLOB = "R-31842-04164"
"""SQLite: zeroblob(N) returns a BLOB of N zero bytes."""
IIF = "R-04218-35309"
"""SQLite: iif(X,Y,Z) is the same as CASE WHEN X THEN Y ELSE Z END."""
NULLIF = "R-29649-49812"
"""SQLite: nullif(X,Y) is X when the arguments differ, else NULL."""
NULLIF_COLLATION = "R-64107-03133"
"""SQLite: nullif(X,Y) uses the collation of the left-most argument that has one."""
MIN = "R-02811-30532"
"""SQLite: the multi-argument min() returns the least argument."""
MAX = "R-60099-10331"
"""SQLite: the multi-argument max() returns the greatest argument, or NULL for a NULL argument."""
MINMAX_COLLATION = "R-17066-08509"
"""SQLite: min() uses the collation of the left-most argument that has one."""
IFNULL = "R-47349-36088"
"""SQLite: ifnull() is coalesce() with two arguments."""
IFNULL_ARGUMENTS = "R-35443-03595"
"""SQLite: ifnull() must have exactly 2 arguments."""
LIKELIHOOD = "R-41921-05214"
"""SQLite: likelihood(X,Y) returns X unchanged."""
LIKELIHOOD_CONSTANT = "R-44133-61651"
"""SQLite: Y in likelihood(X,Y) must be a floating point constant between 0.0 and 1.0."""
UNLIKELY = "R-11152-23456"
"""SQLite: unlikely(X) returns X unchanged."""
LIKE = "R-16584-60189"
"""SQLite: the LIKE operator does a pattern matching comparison."""
GLOB = "R-52087-12043"
"""SQLite: GLOB is like LIKE but with the Unix file globbing syntax."""
ESCAPE = "R-11093-24211"
"""SQLite: the ESCAPE clause gives the escape character of LIKE."""
LOWER = "R-31312-33516"
"""SQLite: lower(X) returns X with all ASCII characters in lower case."""
UPPER = "R-35553-21226"
"""SQLite: upper(X) returns X with all ASCII characters in upper case."""
SUBSTR = "R-64130-24369"
"""SQLite: substr(X,Y,Z) returns the substring of X from the Y-th character, Z characters long."""
INSTR = "R-27549-59611"
"""SQLite: instr(X,Y) finds the first occurrence of Y in X."""
REPLACE = "R-21182-58169"
"""SQLite: replace(X,Y,Z) replaces every occurrence of Y in X with Z."""
TRIM = "R-50629-09283"
"""SQLite: trim(X,Y) removes the characters of Y from both ends of X."""
LTRIM = "R-64249-42392"
"""SQLite: ltrim(X,Y) removes the characters of Y from the left side of X."""
HEX = "R-57089-20897"
"""SQLite: hex() interprets its argument as a BLOB and renders it in upper-case hexadecimal."""
UNHEX = "R-11344-60106"
"""SQLite: unhex(X,Y) decodes the hexadecimal X, skipping the characters of Y."""
QUOTE = "R-38536-04510"
"""SQLite: quote(X) returns the text of an SQL literal that is the value of X."""
CHAR = "R-55469-62130"
"""SQLite: char(X1,...,XN) returns the text of the characters of the code points."""
UNICODE = "R-29701-50711"
"""SQLite: unicode(X) returns the code point of the first character of X."""
UNISTR = "R-27118-60489"
"""SQLite: unistr(X) replaces the escapes of X with their characters."""
CONCAT = "R-07264-38747"
"""SQLite: concat(X,...) returns the concatenation of the text of the arguments that are not NULL."""


def definitions() -> list[QueryCase]:
    """The coverage cases of slice 1 of ADR 0015."""
    case = QueryCase
    return [
        case("function-no-such", TABLES, "SELECT nosuch(i) FROM v;", (ABS,), ("functions", "prepare-error")),
        case("function-no-such-argument-first", TABLES, "SELECT nosuch(nocol) FROM v;", (ABS,),
             ("functions", "prepare-error")),
        case("function-argument-count", TABLES, "SELECT ABS(i, 1) FROM v;", (ABS,), ("functions", "prepare-error")),
        case("function-ifnull-count", TABLES, "SELECT ifnull(i) FROM v;", (IFNULL_ARGUMENTS,),
             ("functions", "prepare-error")),
        case("function-star", TABLES, "SELECT typeof(*) FROM v;", (TYPEOF,), ("functions", "prepare-error")),
        case("function-typeof", TABLES, "SELECT typeof(i), typeof(r), typeof(t), typeof(b), typeof(k) FROM v;",
             (TYPEOF,), ("functions", "typeof")),
        case("function-length", TABLES, "SELECT length(i), length(r), length(t), length(b), length(x'610062'), "
             "length(CAST(x'610062' AS TEXT)) FROM v;", (LENGTH,), ("functions", "length")),
        case("function-octet-length", TABLES, "SELECT octet_length(t), octet_length(b), octet_length(r) FROM v;",
             (OCTET_LENGTH,), ("functions", "length")),
        case("function-abs", TABLES, "SELECT abs(i), abs(r), abs(t), abs(b), abs('x') FROM v;", (ABS,),
             ("functions", "abs")),
        case("function-abs-overflow", TABLES, "SELECT abs(-9223372036854775807 - 1);", (ABS_OVERFLOW,),
             ("functions", "abs", "runtime-error")),
        case("function-sign", TABLES, "SELECT sign(i), sign(r), sign(t), sign(b), sign('2.5') FROM v;",
             (SIGN, SIGN_OTHER), ("functions", "sign")),
        case("function-zeroblob", TABLES, "SELECT zeroblob(3), zeroblob(-1), zeroblob(0), typeof(zeroblob(1));",
             (ZEROBLOB,), ("functions", "zeroblob")),
        case("function-iif", TABLES, "SELECT iif(i, 'yes', 'no'), iif(i > 0, 1), if(r, 'a', t, 'b', 'c'), "
             "iif(0, 1, 0, 2, 3) FROM v;", (IIF,), ("functions", "iif")),
        case("function-nullif", TABLES, "SELECT nullif(i, 0), nullif(n, 'ABC'), nullif('a', n) FROM v;",
             (NULLIF, NULLIF_COLLATION), ("functions", "nullif")),
        case("function-min-max", TABLES, "SELECT min(i, 1), max(i, r, 2), min(t, n), max(n, 'b'), "
             "min('B', 'a' COLLATE nocase) FROM v;", (MIN, MAX, MINMAX_COLLATION), ("functions", "min", "max")),
        case("function-ifnull-likely", TABLES, "SELECT ifnull(i, 'none'), likely(t), unlikely(r), "
             "likelihood(k, 0.5) FROM v;", (IFNULL, LIKELIHOOD, UNLIKELY), ("functions", "likely")),
        case("function-likelihood-constant", TABLES, "SELECT likelihood(k, 1) FROM v;", (LIKELIHOOD_CONSTANT,),
             ("functions", "prepare-error")),
        case("function-like", TABLES, "SELECT t LIKE 'h%', t LIKE '_é%', n LIKE 'a%', t NOT LIKE '%c', "
             "i LIKE '-%', b LIKE 'a' FROM v;", (LIKE,), ("functions", "like")),
        case("function-like-case", TABLES, "SELECT 'ÀB' LIKE 'àb', 'ABC' LIKE 'abc', like('a%', 'ABC');", (LIKE,),
             ("functions", "like")),
        case("function-like-escape", TABLES, "SELECT t LIKE 'a!_c' ESCAPE '!', t LIKE 'a%' ESCAPE '%', "
             "t LIKE '%' ESCAPE NULL FROM v;", (ESCAPE, LIKE), ("functions", "like", "escape")),
        case("function-like-escape-error", TABLES, "SELECT 'abc' LIKE 'a' ESCAPE 'xy';", (ESCAPE,),
             ("functions", "like", "runtime-error")),
        case("function-glob", TABLES, "SELECT t GLOB 'h*', t GLOB '[a-c]?c', t GLOB '[^a]*', n GLOB 'a*', "
             "glob('*1*', i) FROM v;", (GLOB,), ("functions", "glob")),
        case("function-where-order", TABLES, "SELECT k, length(t) AS size FROM v WHERE t LIKE '%l%' OR "
             "typeof(r) = 'null' ORDER BY size DESC, k;", (LIKE, LENGTH), ("functions", "where", "order-by")),
        case("function-values-update", TABLES, "INSERT INTO v(k, i, t) VALUES(5, abs(-5), typeof(1.5)); "
             "UPDATE v SET t = iif(k = 5, 'five', t), i = max(i, 100) WHERE k >= 4; SELECT k, i, t FROM v;",
             (ABS, IIF, MAX), ("functions", "values", "update")),
        case("function-lower-upper", TABLES, "SELECT lower(t), upper(t), lower(n), upper('àb'), lower(r), "
             "upper(b) FROM v;", (LOWER, UPPER), ("functions", "lower", "upper")),
        case("function-substr", TABLES, "SELECT substr(t, 2), substr(t, 2, 2), substr(t, -2), substr(t, 0, 2), "
             "substr(t, -9, 3), substr(t, 3, -2), substring(b, 2), substr(i, 2) FROM v;", (SUBSTR,),
             ("functions", "substr")),
        case("function-substr-edges", TABLES, "SELECT quote(substr(x'', 1)), quote(substr(x'0102', 5)), "
             "substr('abc', NULL), substr('abc', 1, NULL), substr('héllo', -3, -1);", (SUBSTR,),
             ("functions", "substr")),
        case("function-instr", TABLES, "SELECT instr(t, 'l'), instr(t, ''), instr(t, 'z'), instr(b, x'02'), "
             "instr(i, '7'), instr('héllo', 'l') FROM v;", (INSTR,), ("functions", "instr")),
        case("function-replace", TABLES, "SELECT replace(t, 'l', 'L'), replace(t, '', 'x'), replace(t, 'l', ''), "
             "replace(i, '7', 'seven'), replace('aaa', 'aa', 'b') FROM v;", (REPLACE,), ("functions", "replace")),
        case("function-trim", TABLES, "SELECT trim('  a  '), ltrim('  a  '), rtrim('  a  '), trim(t, 'ho'), "
             "ltrim(t, 'éh'), rtrim(t, ''), trim(t, NULL) FROM v;", (TRIM, LTRIM), ("functions", "trim")),
        case("function-hex-unhex", TABLES, "SELECT hex(t), hex(b), hex(i), hex(NULL), quote(unhex('0aFF')), "
             "quote(unhex('0a-ff', '-')), unhex('0a-ff'), unhex('abc') FROM v;", (HEX, UNHEX),
             ("functions", "hex", "unhex")),
        case("function-quote", TABLES, "SELECT quote(i), quote(r), quote(t), quote(b), quote(0.1), quote(1.0/3), "
             "quote(1e15), quote(123456789012345678.0), quote(-0.0), quote('it''s') FROM v;", (QUOTE,),
             ("functions", "quote")),
        case("function-unistr-quote", TABLES, "SELECT unistr_quote(t), unistr_quote(char(97, 10, 98, 39)), "
             r"unistr_quote('x\y'), unistr_quote(r) FROM v;", (QUOTE,), ("functions", "quote")),
        case("function-char-unicode", TABLES, "SELECT char(72, 233, 128512), char(-1), char(), unicode(t), "
             "unicode(''), unicode(i), length(char(97, 0, 98)) FROM v;", (CHAR, UNICODE),
             ("functions", "char", "unicode")),
        case("function-unistr", TABLES, r"SELECT unistr('a\u00e9b'), unistr('\\'), unistr('\+01F600'), "
             r"unistr('\U0001F600'), unistr('\00e9');", (UNISTR,), ("functions", "unistr")),
        case("function-unistr-error", TABLES, r"SELECT unistr('a\xb');", (UNISTR,),
             ("functions", "unistr", "runtime-error")),
        case("function-concat", TABLES, "SELECT concat(t, NULL, i), concat_ws('-', t, NULL, i, r), "
             "concat_ws(NULL, t), concat(b, 'x') FROM v;", (CONCAT,), ("functions", "concat")),
        case("function-aggregate-misuse", TABLES, "SELECT k FROM v WHERE sum(i) > 0;", (ABS,),
             ("functions", "prepare-error")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `text-functions`."""
    return query_records(definitions() if cases is None else cases, part="text-functions")
