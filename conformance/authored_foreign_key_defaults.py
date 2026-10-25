"""Authored cases of ADD COLUMN defaults beside foreign keys (task "foreign-key facts and preservation").

SQLite 3.51.0 refuses `ALTER TABLE ... ADD COLUMN ... REFERENCES ... DEFAULT x` on a nonempty table while
foreign keys are enforced, unless the last DEFAULT is the bare literal NULL (`sqlite3AlterFinishAddColumn`).
The cases extend `conformance.authored_add_references` with the other defaults (text, number, keyword,
time keyword), the other column constraints that the check meets (NOT NULL, CHECK, STRICT, a deferral
clause), a missing parent, and the NOT NULL columns without a REFERENCES clause, for which the model
decides only the literal NULL (`tests/add_column_not_null_default_test.py` compares the other spellings).
Native SQLite is the only source of outcomes. The cases use `conformance.authored_queries.QueryCase`;
a case with the feature `unenforced` runs with foreign keys off.
"""

from conformance.authored_add_references import (
    ADD_REFERENCE, ADD_REFERENCE_ENFORCED, PARENT, POPULATED, REQUIREMENTS, SHOW)
from conformance.authored_queries import QueryCase

ADD_NOT_NULL = "R-29868-13536"
"""SQLite: a NOT NULL column added by ALTER TABLE needs a default value other than NULL."""
ADD_NO_CLOCK = "R-37287-38238"
"""SQLite: an added column may not have a time keyword or a parenthesized expression as its default."""
ADD_COLUMN = "R-10948-48115"
"""SQLite: the ADD COLUMN syntax adds a new column to an existing table."""
STRICT_POPULATED = ("CREATE TABLE p(k PRIMARY KEY); INSERT INTO p VALUES(1), (99); "
                    "CREATE TABLE c(a INTEGER) STRICT; INSERT INTO c VALUES(5), (6);")
"""A parent and a STRICT child table with two rows."""
PLAIN = "CREATE TABLE c(a); INSERT INTO c VALUES(5), (6);"
"""A child table with two rows and no parent."""


def add(column: str) -> str:
    """The migration that adds the column to the child table and shows the table afterwards."""
    return f"ALTER TABLE c ADD COLUMN {column};" + SHOW


def definitions() -> list[QueryCase]:
    """The cases of the ADD COLUMN defaults, in the order of the module description."""
    case = QueryCase
    reference = "y REFERENCES p(k) "
    return [
        case("add-reference-omitted", POPULATED, add(reference), REQUIREMENTS, ("add-column", "references", "omitted")),
        case("add-reference-text", POPULATED, add(reference + "DEFAULT 'x'"), REQUIREMENTS,
             ("add-column", "references", "text")),
        case("add-reference-number", POPULATED, add(reference + "DEFAULT 5"), REQUIREMENTS,
             ("add-column", "references", "number")),
        case("add-reference-keyword", POPULATED, add(reference + "DEFAULT TRUE"), REQUIREMENTS,
             ("add-column", "references", "keyword")),
        case("add-reference-clock", POPULATED, add(reference + "DEFAULT CURRENT_TIMESTAMP"),
             (ADD_REFERENCE, ADD_NO_CLOCK), ("add-column", "references", "clock")),
        case("add-reference-clock-empty", PARENT, add(reference + "DEFAULT CURRENT_TIMESTAMP"),
             (ADD_REFERENCE, ADD_NO_CLOCK), ("add-column", "references", "clock", "empty")),
        case("add-reference-clock-unenforced", POPULATED, add(reference + "DEFAULT CURRENT_TIMESTAMP"),
             (ADD_REFERENCE, ADD_NO_CLOCK), ("add-column", "references", "clock", "unenforced")),
        case("add-reference-not-null-default", POPULATED, add(reference + "NOT NULL DEFAULT 99"), REQUIREMENTS,
             ("add-column", "references", "not-null")),
        case("add-reference-not-null-null", POPULATED, add(reference + "NOT NULL DEFAULT NULL"),
             (ADD_REFERENCE_ENFORCED, ADD_NOT_NULL), ("add-column", "references", "not-null", "null")),
        case("add-reference-check", POPULATED, add(reference + "CHECK(y IS NULL) DEFAULT 99"), REQUIREMENTS,
             ("add-column", "references", "check")),
        case("add-reference-deferred", POPULATED,
             add("y DEFAULT 99 REFERENCES p(k) ON DELETE CASCADE DEFERRABLE INITIALLY DEFERRED"), REQUIREMENTS,
             ("add-column", "references", "deferred")),
        case("add-reference-missing-parent", POPULATED, add("y REFERENCES nope DEFAULT 5"), REQUIREMENTS,
             ("add-column", "references", "missing-parent")),
        case("add-reference-missing-parent-null", POPULATED,
             "ALTER TABLE c ADD COLUMN y REFERENCES nope; PRAGMA foreign_key_check;"
             " INSERT INTO c(a) VALUES(7); SELECT * FROM c;", REQUIREMENTS,
             ("add-column", "references", "missing-parent", "null")),
        case("add-reference-strict", STRICT_POPULATED, add("y INTEGER REFERENCES p(k) DEFAULT 99"), REQUIREMENTS,
             ("add-column", "references", "strict")),
        case("add-default-without-reference", PLAIN, add("y DEFAULT 99"), (ADD_COLUMN,),
             ("add-column", "default", "control")),
        case("add-not-null-null", PLAIN, add("y INT NOT NULL DEFAULT NULL"), (ADD_NOT_NULL,),
             ("add-column", "not-null", "null")),
        case("add-not-null-null-empty", "CREATE TABLE c(a);", add("y INT NOT NULL DEFAULT NULL"), (ADD_NOT_NULL,),
             ("add-column", "not-null", "null", "empty")),
        case("add-not-null-number", PLAIN, add("y INT NOT NULL DEFAULT 7"), (ADD_NOT_NULL,),
             ("add-column", "not-null", "number")),
        case("add-not-null-omitted", PLAIN, add("y INT NOT NULL"), (ADD_NOT_NULL,),
             ("add-column", "not-null", "omitted")),
    ]
