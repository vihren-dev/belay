"""Authored cases of the foreign-key parent mapping and the actions beside it (task "foreign-key facts and
preservation").

SQLite compares a child key against the parent key columns that the engine selects, which differ from
the declared columns when the parent key repeats a column: with `PRIMARY KEY(a, a)` the foreign key
`(x, y) REFERENCES p(a, b)` reads the child column `x` twice and never reads `y`. The cases cover the
NULL test through that selection (insert, update, parent delete, parent update, `foreign_key_check`),
the actions on the selected columns, the actions beside RESTRICT, NO ACTION and SET DEFAULT with and
without a parent for the default, and a CREATE INDEX over a repeated column that turns a row the
check exempted into a violation. Native SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase`; a case with the feature `unenforced` runs with foreign keys off.
"""

from conformance.authored_queries import QueryCase
from conformance.foreign_key_requirements import (
    CASCADE_UPDATE, COMPOSITE_NULL, DEFAULT_MISSING, MISSING, NO_ACTION, RESTRICT, RESTRICT_AT_ONCE, SATISFIED,
    SET_DEFAULT, SET_NULL)
from conformance.pragma_requirements import FK_CHECK

PARENT_KEY = "R-13435-26311"
"""SQLite: the parent key columns must be the primary key or have a UNIQUE index."""
REPEATED = "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); "
"""A parent whose key repeats the column a."""
ONE_PARENT_ROW = "INSERT INTO p VALUES(1,2); "
"""The parent row that the cases of the repeated key share."""
NO_ACTION_TRIGGER = ("CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k) ON DELETE NO ACTION); "
                     "CREATE TRIGGER back AFTER DELETE ON p BEGIN INSERT INTO p VALUES(old.k); END; "
                     "INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);")
"""A child with NO ACTION, and a trigger that puts each deleted parent row back."""
RESTRICT_TRIGGER = NO_ACTION_TRIGGER.replace("NO ACTION", "RESTRICT")
"""The same schema with RESTRICT, which reports the child as soon as the parent row goes."""
RESTRICT_PLAIN = ("CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k) ON DELETE RESTRICT); "
                  "INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);")
"""A child with RESTRICT and no trigger."""
SET_DEFAULT_PLAIN = ("CREATE TABLE p(k PRIMARY KEY); "
                     "CREATE TABLE c(x DEFAULT 0 REFERENCES p(k) ON DELETE SET DEFAULT ON UPDATE SET DEFAULT); "
                     "INSERT INTO p VALUES(0),(1); INSERT INTO c VALUES(1);")
"""A child whose default 0 has a parent row."""
SET_DEFAULT_MISSING = ("CREATE TABLE p(k PRIMARY KEY); "
                       "CREATE TABLE c(x DEFAULT 0 REFERENCES p(k) ON DELETE SET DEFAULT); "
                       "INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);")
"""A child whose default 0 has no parent row."""
INDEX_SETUP = ("CREATE TABLE p(a,b); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b)); "
               "INSERT INTO c VALUES(99,NULL);")
"""A parent without a unique index and a child row (99, NULL), stored while foreign keys are off."""


def child(actions: str = "", defaults: str = "x,y") -> str:
    """The child of the repeated key, with the columns x and y and the actions on the foreign key."""
    return f"CREATE TABLE c({defaults},FOREIGN KEY(x,y) REFERENCES p(a,b){actions}); "


def definitions() -> list[QueryCase]:
    """All cases of the parent mapping and of the actions, in the order of the module description."""
    case = QueryCase
    plain = REPEATED + child()
    kept = plain + ONE_PARENT_ROW
    orphan = kept + "INSERT INTO c VALUES(1,NULL); "
    cascade = REPEATED + child(" ON UPDATE CASCADE") + ONE_PARENT_ROW + "INSERT INTO c VALUES(1,99); "
    defaults = REPEATED + child(" ON DELETE SET DEFAULT", "x DEFAULT 3,y DEFAULT 4")
    return [
        case("mapped-unused-value", plain, "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99);"
             " PRAGMA foreign_key_check;", (SATISFIED, PARENT_KEY), ("mapping", "repeated", "value")),
        case("mapped-null-unused-insert", kept, "INSERT INTO c VALUES(99,NULL);", (MISSING, COMPOSITE_NULL),
             ("mapping", "null", "unused", "insert")),
        case("mapped-null-unused-pragma", kept + "INSERT INTO c VALUES(99,NULL); ", "PRAGMA foreign_key_check;",
             (FK_CHECK, COMPOSITE_NULL), ("mapping", "null", "unused", "pragma", "unenforced")),
        case("mapped-null-selected-insert", kept, "INSERT INTO c VALUES(NULL,99); PRAGMA foreign_key_check;",
             (SATISFIED, COMPOSITE_NULL), ("mapping", "null", "selected", "insert")),
        case("mapped-null-unused-update", orphan, "UPDATE c SET x=99;", (MISSING, COMPOSITE_NULL),
             ("mapping", "null", "unused", "update")),
        case("mapped-null-selected-update", kept + "INSERT INTO c VALUES(1,99); ",
             "UPDATE c SET x=NULL; PRAGMA foreign_key_check;", (SATISFIED, COMPOSITE_NULL),
             ("mapping", "null", "selected", "update")),
        case("mapped-null-parent-delete", orphan, "DELETE FROM p;", (MISSING, COMPOSITE_NULL),
             ("mapping", "null", "parent", "delete")),
        case("mapped-null-parent-update", orphan, "UPDATE p SET a=99;", (MISSING, COMPOSITE_NULL),
             ("mapping", "null", "parent", "update")),
        case("mapped-null-cascade", REPEATED + child(" ON UPDATE CASCADE") + ONE_PARENT_ROW
             + "INSERT INTO c VALUES(1,NULL); ", "UPDATE p SET a=99; PRAGMA foreign_key_check;",
             (CASCADE_UPDATE, COMPOSITE_NULL), ("mapping", "null", "cascade")),
        case("mapped-missing-composite-null", "CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));"
             " INSERT INTO c VALUES(99,NULL); ", "PRAGMA foreign_key_check;", (FK_CHECK, COMPOSITE_NULL),
             ("mapping", "null", "missing-parent", "unenforced")),
        case("mapped-cascade-unused-column", cascade, "UPDATE p SET a=2; SELECT x,y FROM c;",
             (CASCADE_UPDATE,), ("mapping", "action", "cascade")),
        case("mapped-set-null-unused-column", REPEATED + child(" ON DELETE SET NULL") + ONE_PARENT_ROW
             + "INSERT INTO c VALUES(1,99); ", "DELETE FROM p; SELECT x,y FROM c;", (SET_NULL,),
             ("mapping", "action", "set-null", "delete")),
        case("mapped-set-null-update", REPEATED + child(" ON UPDATE SET NULL") + ONE_PARENT_ROW
             + "INSERT INTO c VALUES(1,99); ", "UPDATE p SET a=2; SELECT x,y FROM c;", (SET_NULL,),
             ("mapping", "action", "set-null", "update")),
        case("mapped-set-default-unused-column",
             defaults + "INSERT INTO p VALUES(1,2),(3,4); INSERT INTO c VALUES(1,99); ",
             "DELETE FROM p WHERE a=1; SELECT x,y FROM c;", (SET_DEFAULT,),
             ("mapping", "action", "set-default", "delete")),
        case("mapped-set-default-update", REPEATED + child(" ON UPDATE SET DEFAULT", "x DEFAULT 3,y DEFAULT 4")
             + "INSERT INTO p VALUES(1,2),(3,4); INSERT INTO c VALUES(1,99); ",
             "UPDATE p SET a=2 WHERE a=1; SELECT x,y FROM c;", (SET_DEFAULT,),
             ("mapping", "action", "set-default", "update")),
        case("mapped-action-trigger-columns", cascade + "CREATE TABLE log(k); ",
             "CREATE TRIGGER used AFTER UPDATE OF x ON c BEGIN INSERT INTO log VALUES('x'); END;"
             " CREATE TRIGGER unused AFTER UPDATE OF y ON c BEGIN INSERT INTO log VALUES('y'); END;"
             " UPDATE p SET a=2; SELECT x,y FROM c; SELECT k FROM log ORDER BY k;", (CASCADE_UPDATE,),
             ("mapping", "action", "trigger-columns")),
        case("mapped-ordinary-composite-order", "CREATE TABLE p(a,b,PRIMARY KEY(b,a)); "
             + child(" ON UPDATE CASCADE") + "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,2); ",
             "UPDATE p SET a=3,b=4; SELECT x,y FROM c;", (CASCADE_UPDATE, PARENT_KEY),
             ("mapping", "action", "composite")),
        case("mapped-rowid-parent-actions", "CREATE TABLE p(k INTEGER PRIMARY KEY);"
             " CREATE TABLE c(x REFERENCES p ON UPDATE CASCADE ON DELETE SET NULL,y);"
             " INSERT INTO p VALUES(1); INSERT INTO c VALUES(1,99); ",
             "UPDATE p SET k=2; SELECT x,y FROM c; DELETE FROM p; SELECT x,y FROM c;", (CASCADE_UPDATE, SET_NULL),
             ("mapping", "action", "rowid")),
        case("action-no-action-repaired", NO_ACTION_TRIGGER, "DELETE FROM p; SELECT * FROM p; SELECT * FROM c;",
             (NO_ACTION,), ("action", "no-action", "trigger")),
        case("action-restrict-not-repaired", RESTRICT_TRIGGER, "DELETE FROM p; SELECT * FROM p; SELECT * FROM c;",
             (RESTRICT, RESTRICT_AT_ONCE), ("action", "restrict", "trigger")),
        case("action-restrict-unenforced", RESTRICT_PLAIN,
             "DELETE FROM p; SELECT * FROM p; PRAGMA foreign_key_check;", (RESTRICT, FK_CHECK),
             ("action", "restrict", "unenforced")),
        case("action-set-default-delete", SET_DEFAULT_PLAIN, "DELETE FROM p WHERE k = 1; SELECT * FROM c;",
             (SET_DEFAULT,), ("action", "set-default", "delete")),
        case("action-set-default-update", SET_DEFAULT_PLAIN, "UPDATE p SET k = 2 WHERE k = 1; SELECT * FROM c;",
             (SET_DEFAULT,), ("action", "set-default", "update")),
        case("action-set-default-without-parent", SET_DEFAULT_MISSING, "DELETE FROM p; SELECT * FROM p;",
             (SET_DEFAULT, DEFAULT_MISSING), ("action", "set-default", "missing-parent")),
        case("index-repeated-column-reports", INDEX_SETUP,
             "CREATE UNIQUE INDEX pk ON p(a,a); PRAGMA foreign_key_check;", (FK_CHECK, PARENT_KEY),
             ("index", "repeated", "unenforced")),
        case("index-distinct-columns-exempt", INDEX_SETUP,
             "CREATE UNIQUE INDEX pk ON p(a,b); PRAGMA foreign_key_check;", (FK_CHECK, PARENT_KEY),
             ("index", "distinct", "unenforced")),
    ]
