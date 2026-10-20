"""Authored coverage cases of index forms (ADR 0014, slice 1).

The cases follow the "Tests" list of the slice 1 task: an expression index that refuses rows
equal under the expression and admits rows that differ; a partial unique index that admits
two rows outside its filter and refuses two inside it; REPLACE, IGNORE and UPSERT over a
partial unique index; a constant key term; an UPDATE into equal expression keys; CREATE
INDEX in a migration over existing rows, unique and not, with and without a filter; sort
orders; and the prepare errors of index terms and filters, except the time keywords,
which the recorder refuses outside a controlled clock (the Lean examples of
`Resolution/IndexExamples.lean` cover them). Native SQLite is the only
source of outcomes. The cases use `conformance.authored_queries.QueryCase` and its
recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE p(a INTEGER, b INTEGER); CREATE UNIQUE INDEX pu ON p(a) WHERE b IS NOT NULL; "
          "CREATE TABLE s(a INTEGER, b INTEGER); CREATE UNIQUE INDEX ss ON s(a + b); "
          "CREATE TABLE c(a INTEGER); CREATE UNIQUE INDEX cc ON c(5); "
          "CREATE TABLE d(a INTEGER, b TEXT); "
          "INSERT INTO p VALUES(1, NULL); INSERT INTO s VALUES(1, 2); "
          "INSERT INTO d VALUES(1, 'x'), (1, 'y'), (2, 'x');")
"""A table with a partial unique index, one with a unique expression index, one with a
unique index of a constant, and one without indexes whose rows repeat a value."""

UNIQUE_INDEX = "R-06718-34797"
"""SQLite: with UNIQUE between CREATE and INDEX, duplicate index entries are not allowed."""
PARTIAL_UNIQUE = "R-45667-58607"
"""SQLite: a partial index with UNIQUE requires every entry of the index to be unique."""
PARTIAL_ROWS = "R-59958-37183"
"""SQLite: only rows for which the WHERE clause is true are included in a partial index."""
PARTIAL_NULL = "R-36357-08369"
"""SQLite: rows for which the WHERE clause is NULL or false are omitted from the index."""
FILTER_COLUMNS = "R-41796-02552"
"""SQLite: the WHERE clause of a partial index may name any column of the table."""
EXPRESSION_COLUMNS = "R-40025-59984"
"""SQLite: expressions in an index may only refer to columns of the indexed table."""
EXPRESSION_KEY = "R-06603-49335"
"""SQLite: `index_xinfo` reports -2 as the column of an expression key."""
DESCENDING = "R-32925-06786"
"""SQLite: an index column may be ASC or DESC."""
CREATE_INDEX = "R-57025-62168"
"""SQLite: CREATE INDEX adds an index to an existing table."""


def definitions() -> list[QueryCase]:
    """The coverage cases of index forms."""
    case = QueryCase
    return [
        case("index-expression-conflict", TABLES, "INSERT INTO s VALUES(2, 1);", (UNIQUE_INDEX, EXPRESSION_KEY),
             ("index", "expression", "constraint")),
        case("index-expression-distinct", TABLES, "INSERT INTO s VALUES(2, 2), (0, 0) RETURNING a, b;",
             (UNIQUE_INDEX, EXPRESSION_KEY), ("index", "expression")),
        case("index-expression-update", TABLES, "INSERT INTO s VALUES(5, 5); UPDATE s SET a = 2, b = 1 WHERE a = 5;",
             (UNIQUE_INDEX,), ("index", "expression", "update", "constraint")),
        case("index-constant-key", TABLES, "INSERT INTO c VALUES(1); INSERT INTO c VALUES(2);", (UNIQUE_INDEX,),
             ("index", "expression", "constant", "constraint")),
        case("index-partial-outside", TABLES, "INSERT INTO p VALUES(1, NULL), (2, NULL) RETURNING a, b;",
             (PARTIAL_ROWS, PARTIAL_NULL), ("index", "partial")),
        case("index-partial-inside", TABLES, "INSERT INTO p VALUES(1, 2); INSERT INTO p VALUES(1, 3);",
             (PARTIAL_UNIQUE, FILTER_COLUMNS), ("index", "partial", "constraint")),
        case("index-partial-replace", TABLES, "INSERT INTO p VALUES(1, 2); INSERT OR REPLACE INTO p VALUES(1, 3);",
             (PARTIAL_UNIQUE,), ("index", "partial", "replace")),
        case("index-partial-ignore", TABLES, "INSERT INTO p VALUES(1, 2); INSERT OR IGNORE INTO p VALUES(1, 4);",
             (PARTIAL_UNIQUE,), ("index", "partial", "ignore")),
        case("index-partial-target", TABLES, "INSERT INTO p VALUES(1, 2) ON CONFLICT(a) DO NOTHING;",
             (PARTIAL_UNIQUE,), ("index", "partial", "on-conflict", "prepare-error")),
        case("index-runs", TABLES, "CREATE INDEX da ON d(a); INSERT INTO d VALUES(1, 'z');", (CREATE_INDEX,),
             ("index", "create-index")),
        case("index-runs-unique-duplicates", TABLES, "CREATE UNIQUE INDEX da ON d(a); INSERT INTO d VALUES(3, 'w');",
             (CREATE_INDEX, UNIQUE_INDEX), ("index", "create-index", "constraint")),
        case("index-runs-unique", TABLES, "CREATE UNIQUE INDEX db ON d(a, b); INSERT INTO d VALUES(1, 'x');",
             (CREATE_INDEX, UNIQUE_INDEX), ("index", "create-index", "constraint")),
        case("index-runs-partial", TABLES, "CREATE UNIQUE INDEX dp ON d(a) WHERE b = 'y'; INSERT INTO d VALUES(1, 'y');",
             (CREATE_INDEX, PARTIAL_UNIQUE), ("index", "create-index", "partial", "constraint")),
        case("index-runs-expression", TABLES, "CREATE UNIQUE INDEX de ON d(a * 0 + 7);", (CREATE_INDEX, UNIQUE_INDEX),
             ("index", "create-index", "expression", "constraint")),
        case("index-descending", TABLES, "CREATE INDEX dd ON d(a DESC, b); INSERT INTO d VALUES(4, 'v');",
             (CREATE_INDEX, DESCENDING), ("index", "create-index", "descending")),
        case("index-qualified-term", TABLES, "CREATE INDEX dq ON d(d.a);", (EXPRESSION_COLUMNS,),
             ("index", "prepare-error")),
        case("index-qualified-filter", TABLES, "CREATE INDEX dq ON d(a) WHERE d.b = 'x';", (FILTER_COLUMNS,),
             ("index", "partial", "create-index")),
        case("index-missing-filter-column", TABLES, "CREATE INDEX dm ON d(a) WHERE zz > 0;", (FILTER_COLUMNS,),
             ("index", "partial", "prepare-error")),
        case("index-rowid-term", TABLES, "CREATE INDEX dr ON d(rowid);", (EXPRESSION_COLUMNS,),
             ("index", "prepare-error")),
        case("index-aggregate-term", TABLES, "CREATE INDEX dg ON d(count(a));", (EXPRESSION_COLUMNS,),
             ("index", "prepare-error")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `indexes`."""
    return query_records(definitions() if cases is None else cases, part="indexes")
