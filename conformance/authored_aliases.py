"""Authored coverage cases of rowid aliases (ADR 0012, amendment 4, slice 5b).

The cases follow the "Tests" list of the slice 5b task: each declaration form (column and
table constraint, lower case, `NOT NULL`, and `DESC` and `INT` as ordinary columns);
INSERT of NULL, omitted, negative, explicit, `' 7 '` and `'8.0'` aliases, and of `'0x10'`,
`1.5`, `1e20` and a BLOB, which are `datatype mismatch`; a duplicate alias; the order of a
mismatch and a unique failure; the next rowid after an explicit alias; `RETURNING` of the
alias; UPDATE of the alias to a new value, a duplicate, NULL and text; and a query that
reads the alias. Native SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE i(id INTEGER PRIMARY KEY, v TEXT); CREATE TABLE lc(id integer primary key, v); "
          "CREATE TABLE tc(id INTEGER, v, PRIMARY KEY(id)); CREATE TABLE nn(id INTEGER PRIMARY KEY NOT NULL, v); "
          "CREATE TABLE ds(id INTEGER PRIMARY KEY DESC, v); CREATE TABLE ni(id INT PRIMARY KEY, v); "
          "INSERT INTO i VALUES(1, 'a'), (2, 'b'); INSERT INTO lc VALUES(1, 'a'); INSERT INTO tc VALUES(1, 'a'); "
          "INSERT INTO ds VALUES(1, 'a'); INSERT INTO ni VALUES(1, 'a');")
"""Four tables with a rowid alias in its declaration forms, and two whose INTEGER
`PRIMARY KEY DESC` and `INT PRIMARY KEY` are ordinary key columns."""

ALIAS = "R-38485-20010"
"""SQLite: a column of type INTEGER PRIMARY KEY becomes an alias for the rowid."""
NULL_ROWID = "R-07986-46024"
"""SQLite: inserting NULL into an integer primary key chooses the rowid automatically."""
NEXT_ROWID = "R-29538-34987"
"""SQLite: a new row normally gets a rowid one larger than the largest rowid before the insert."""
MISMATCH = "R-05734-13629"
"""SQLite: a blob, or a string or real that cannot be converted losslessly to an integer,
in an integer primary key is a datatype mismatch."""
NOT_ALIAS = "R-45951-08347"
"""SQLite: an INTEGER column declared PRIMARY KEY DESC is not an alias for the rowid."""
OTHER_TYPES = "R-41444-49665"
"""SQLite: other integer type names, such as INT, make an ordinary primary key column."""
UPDATE = "R-03733-29734"
"""SQLite: rowid values may be modified with UPDATE, also through an alias."""


def definitions() -> list[QueryCase]:
    """The coverage cases of rowid aliases."""
    case = QueryCase
    return [
        case("alias-null", TABLES, "INSERT INTO i VALUES(NULL, 'c') RETURNING id;", (ALIAS, NULL_ROWID),
             ("alias", "insert", "null")),
        case("alias-omitted", TABLES, "INSERT INTO i(v) VALUES('c') RETURNING id;", (ALIAS, NULL_ROWID),
             ("alias", "insert", "omitted")),
        case("alias-negative", TABLES, "INSERT INTO i VALUES(-5, 'c') RETURNING id;", (ALIAS,),
             ("alias", "insert")),
        case("alias-next-after-explicit", TABLES, "INSERT INTO i VALUES(10, 'c'), (NULL, 'd') RETURNING id;",
             (ALIAS, NEXT_ROWID), ("alias", "insert", "next")),
        case("alias-text-integer", TABLES, "INSERT INTO i VALUES(' 7 ', 'c') RETURNING id;", (ALIAS, MISMATCH),
             ("alias", "insert", "affinity")),
        case("alias-text-real-integer", TABLES, "INSERT INTO i VALUES('8.0', 'c') RETURNING id;", (ALIAS, MISMATCH),
             ("alias", "insert", "affinity")),
        case("alias-mismatch-hex", TABLES, "INSERT INTO i VALUES('0x10', 'c');", (MISMATCH,),
             ("alias", "insert", "mismatch")),
        case("alias-mismatch-real", TABLES, "INSERT INTO i VALUES(1.5, 'c');", (MISMATCH,),
             ("alias", "insert", "mismatch")),
        case("alias-mismatch-large", TABLES, "INSERT INTO i VALUES(1e20, 'c');", (MISMATCH,),
             ("alias", "insert", "mismatch")),
        case("alias-mismatch-blob", TABLES, "INSERT INTO i VALUES(x'31', 'c');", (MISMATCH,),
             ("alias", "insert", "mismatch")),
        case("alias-duplicate", TABLES, "INSERT INTO i VALUES(1, 'c');", (ALIAS,), ("alias", "insert", "constraint")),
        case("alias-mismatch-before-duplicate", TABLES, "INSERT INTO i VALUES('x', 'c'), (1, 'd');", (MISMATCH,),
             ("alias", "insert", "order")),
        case("alias-duplicate-before-mismatch", TABLES, "INSERT INTO i VALUES(1, 'c'), ('x', 'd');", (ALIAS,),
             ("alias", "insert", "order")),
        case("alias-lower-case", TABLES, "INSERT INTO lc VALUES(NULL, 'b') RETURNING id;", (ALIAS, NULL_ROWID),
             ("alias", "form")),
        case("alias-table-constraint", TABLES, "INSERT INTO tc VALUES(NULL, 'b') RETURNING id;", (ALIAS, NULL_ROWID),
             ("alias", "form")),
        case("alias-not-null", TABLES, "INSERT INTO nn VALUES(NULL, 'b') RETURNING id;", (ALIAS, NULL_ROWID),
             ("alias", "form", "not-null")),
        case("not-alias-desc", TABLES, "INSERT INTO ds VALUES(1.5, 'b') RETURNING id;", (NOT_ALIAS,),
             ("alias", "form", "desc")),
        case("not-alias-int", TABLES, "INSERT INTO ni VALUES(1.5, 'b') RETURNING id;", (OTHER_TYPES,),
             ("alias", "form", "int")),
        case("alias-update-move", TABLES, "UPDATE i SET id = 9 WHERE v = 'a' RETURNING id, v;", (UPDATE,),
             ("alias", "update")),
        case("alias-update-duplicate", TABLES, "UPDATE i SET id = 2 WHERE v = 'a';", (UPDATE,),
             ("alias", "update", "constraint")),
        case("alias-update-null", TABLES, "UPDATE i SET id = NULL WHERE v = 'a';", (UPDATE, MISMATCH),
             ("alias", "update", "mismatch")),
        case("alias-update-text", TABLES, "UPDATE i SET id = 'z' WHERE v = 'a';", (UPDATE, MISMATCH),
             ("alias", "update", "mismatch")),
        case("alias-update-no-row", TABLES, "UPDATE i SET id = 'z' WHERE v = 'zz';", (UPDATE,),
             ("alias", "update")),
        case("alias-query", TABLES, "SELECT id, v FROM i WHERE id > 1 ORDER BY id DESC;", (ALIAS,),
             ("alias", "query")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `aliases`."""
    return query_records(definitions() if cases is None else cases, part="aliases")
