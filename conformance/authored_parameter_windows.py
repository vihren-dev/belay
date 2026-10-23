"""Authored cases of `LIMIT ?`, `OFFSET ?` and the prepare errors of parameters (outcomes 5 and 6
of plans/20261023-parameters.task.md).

The window cases bind each kind of value that SQLite's `OP_MustBeInt` accepts, and each kind that
fails the statement with `datatype mismatch`. A failed statement ends the run of its case, so each
failing value has its own case. The prepare cases put a parameter in each place where SQLite
refuses it.
"""

from conformance.authored_parameters import NULL, ParameterCase, blob, integer, real, text

ROWS = "CREATE TABLE w(id INTEGER PRIMARY KEY); INSERT INTO w VALUES(1), (2), (3), (4), (5);"
"""Five rows with distinct sort keys, so that each window has one possible result."""
SCHEMA = "CREATE TABLE t(n INTEGER); CREATE TABLE log(x);"
"""A table for the definitions that refuse a parameter, and a table for trigger bodies."""
LIMITED = "SELECT id FROM w ORDER BY id LIMIT ?;"
"""A window whose LIMIT is the bound value."""
OFFSET_ONLY = "SELECT id FROM w ORDER BY id LIMIT 2 OFFSET ?;"
"""A window whose OFFSET is the bound value."""

LIMIT_VALUE = "R-30481-56627"
"""SQLite: the LIMIT expression must evaluate to an integer or a value that converts losslessly."""
OFFSET_VALUE = "R-24188-24349"
"""SQLite: the OFFSET expression must evaluate to such an integer too."""
NEGATIVE_LIMIT = "R-03014-26414"
"""SQLite: a negative LIMIT has no upper bound."""
NEGATIVE_OFFSET = "R-23293-62447"
"""SQLite: a negative OFFSET is the same as zero."""
CONSTANT_DEFAULT = "R-33440-07331"
"""SQLite: a DEFAULT expression with a bound parameter is not constant."""
NEXT_NUMBER, COLON = "R-33670-36097", "R-11620-22743"
"""SQLite: the parameter forms `?` and `:AAAA`. The documentation has no requirement for the refusal
of a parameter in a trigger or a CHECK constraint, so these cases name the form that they use."""
GENERATED_TERMS = "R-24770-07833"
"""SQLite: a generated column may reference only constant literals and columns of its row."""
INDEX_TERMS = "R-40025-59984"
"""SQLite: an index expression may refer only to columns of the indexed table."""
PARTIAL_INDEX = "R-65161-60989"
"""SQLite: the WHERE of a partial index may not contain bound parameters."""

ACCEPTED_LIMITS = (integer(2), real(2.0), text("2"), text(" 2 "), text("+2"), text("2.0"), text("2e0"), integer(-1))
"""Values that LIMIT reads as an integer: 2 in seven forms, and -1 for no limit."""
ACCEPTED_OFFSETS = (integer(1), real(1.0), text(" 1"), text("1.0"), integer(-1))
"""Values that OFFSET reads as an integer: 1 in four forms, and -1 that skips no rows."""
REFUSED = {"null": NULL, "blob": blob(b"\x02"), "empty-text": text(""), "word": text("abc"), "hex-text": text("0x10"),
           "fraction": real(2.5), "fraction-text": text("2.5"), "large-real": real(1e20),
           "large-text": text("9223372036854775808")}
"""Values that fail the statement with `datatype mismatch`, by a name for the case."""


def accepted_cases() -> list[ParameterCase]:
    """Each kind of value that LIMIT and OFFSET accept, and the order in which SQLite reads them.

    The recorder finds the window with `CAST(? AS INTEGER)` (`conformance.native_ordering`). That
    cast reads `'1e1'` as 1 and NULL as NULL, so `'1e1'` limits a query of one row, and the OFFSET
    that a `LIMIT 0` skips is text or a fraction, not NULL."""
    case = ParameterCase
    exponent = "SELECT id FROM w WHERE id = 1 LIMIT ?;"
    return [
        case("parameter-limit-accepted", ROWS, LIMITED * len(ACCEPTED_LIMITS) + exponent,
             (LIMIT_VALUE, NEGATIVE_LIMIT), ("limit", "integer-forms", "negative"),
             tuple((value,) for value in ACCEPTED_LIMITS) + ((text("1e1"),),)),
        case("parameter-offset-accepted", ROWS, OFFSET_ONLY * len(ACCEPTED_OFFSETS),
             (OFFSET_VALUE, NEGATIVE_OFFSET), ("offset", "integer-forms", "negative"),
             tuple((value,) for value in ACCEPTED_OFFSETS)),
        case("parameter-limit-zero-skips-offset", ROWS, "SELECT id FROM w ORDER BY id LIMIT ? OFFSET ?;" * 2,
             (LIMIT_VALUE, OFFSET_VALUE), ("limit", "offset", "read-order", "empty-result"),
             ((integer(0), REFUSED["word"]), (integer(0), REFUSED["fraction"]))),
        case("parameter-limit-comma", ROWS, "SELECT id FROM w ORDER BY id LIMIT ?, ?;",
             (LIMIT_VALUE, "R-33788-46243"), ("limit", "offset", "comma"), ((integer(1), integer(2)),)),
    ]


def refused_cases() -> list[ParameterCase]:
    """Each kind of value that fails LIMIT, a few that fail OFFSET, and the reads of SQLite's
    order: OFFSET after a LIMIT that is not 0, and OFFSET of a query without rows."""
    case = ParameterCase
    limits = [case(f"parameter-limit-refused-{name}", ROWS, LIMITED, (LIMIT_VALUE,), ("limit", "datatype-mismatch"),
                   ((value,),)) for name, value in REFUSED.items()]
    offsets = [case(f"parameter-offset-refused-{name}", ROWS, OFFSET_ONLY, (OFFSET_VALUE,),
                    ("offset", "datatype-mismatch"), ((REFUSED[name],),)) for name in ("null", "fraction", "word")]
    return limits + offsets + [
        case("parameter-offset-read-after-limit", ROWS, "SELECT id FROM w ORDER BY id LIMIT ? OFFSET ?;",
             (OFFSET_VALUE, NEGATIVE_LIMIT), ("limit", "offset", "read-order", "datatype-mismatch"),
             ((integer(-1), NULL),)),
        case("parameter-offset-read-without-rows", ROWS, "SELECT id FROM w WHERE 0 LIMIT 2 OFFSET ?;",
             (OFFSET_VALUE,), ("offset", "read-order", "empty-result", "datatype-mismatch"), ((NULL,),)),
    ]


def prepare_cases() -> list[ParameterCase]:
    """The prepare errors of outcome 6. `DEFAULT ?` without parentheses is a grammar error, which
    the frontend refuses (`tests/syntax_parameters_test.py`), and an expression whose walk of
    names finds another error is the restriction `parameter-error-order`
    (`conformance.restriction_examples`)."""
    case = ParameterCase
    trigger = "CREATE TRIGGER t_log AFTER INSERT ON t "
    statements = {
        "trigger-body": (trigger + "BEGIN INSERT INTO log VALUES(?); END;", (NEXT_NUMBER,)),
        "trigger-when": (trigger + "WHEN new.n > :a BEGIN INSERT INTO log VALUES(new.n); END;", (COLON,)),
        "default": ("CREATE TABLE d(x DEFAULT (?));", (CONSTANT_DEFAULT,)),
        "check": ("CREATE TABLE d(x CHECK (x > ?));", (NEXT_NUMBER,)),
        "generated": ("CREATE TABLE d(x, y AS (x + ?));", (GENERATED_TERMS,)),
        "index-expression": ("CREATE INDEX t_expr ON t(n + ?);", (INDEX_TERMS,)),
        "partial-index": ("CREATE INDEX t_part ON t(n) WHERE n > ?;", (PARTIAL_INDEX,)),
    }
    return [case(f"parameter-prepare-{name}", SCHEMA, sql, requirements, ("prepare-error", name), ((),))
            for name, (sql, requirements) in statements.items()]


def window_definitions() -> list[ParameterCase]:
    """The cases of outcomes 5 and 6."""
    return accepted_cases() + refused_cases() + prepare_cases()
