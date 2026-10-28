"""Native inputs for the table rebuild of the guide (ADR 0019, D4, part 3).

The rebuild creates a new table, copies the rows with INSERT SELECT, drops the old table and renames the new
one. The cases cover the steps together, with the foreign-key behavior that decides whether the rebuild keeps
the child rows: the unsafe rebuild with enforcement on, which cascades; the corrected rebuild, which turns
enforcement off and checks with `foreign_key_check`; the default of a connection with enforcement off; a pragma
inside a transaction, which does nothing; a rename of the old table first, which moves the foreign keys of its
children; a view that blocks the rename; and a rollback of the whole rebuild. The recorder fixes the state of
enforcement at the start of a case, as the measured profile, because a pragma outside a transaction would change the
profile; a case with the feature `fk-on` starts with enforcement on, any other case with SQLite's default (off).
SQLite supplies every outcome through the query recorder.
"""

from conformance.authored_foreign_keys import profile as foreign_key_profile
from conformance.authored_queries import QueryCase
from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.native_record import record_sql

IMPLICIT_DELETE = "R-14208-23986"
"""SQLite: with foreign keys enabled when the statement is prepared, DROP TABLE removes all rows with an implicit DELETE first."""
ACTIONS = "R-56522-34239"
"""SQLite: an implicit DELETE FROM of a DROP TABLE does cause any configured foreign key actions to take place."""
OFF_BY_DEFAULT = "R-09033-01493"
"""SQLite: the default setting for foreign key enforcement is OFF."""
IN_TRANSACTION = "R-53547-37067"
"""SQLite: PRAGMA foreign_keys is a no-op within a transaction."""
CHECK = "R-41653-15278"
"""SQLite: foreign_key_check returns one row for each foreign key violation."""

FAMILY = (
    "CREATE TABLE p(id INTEGER PRIMARY KEY, name TEXT, extra INTEGER); INSERT INTO p VALUES(1,'x',10),(2,'y',20); "
    "CREATE TABLE c(id INTEGER PRIMARY KEY, pid INTEGER REFERENCES p(id) ON DELETE CASCADE, note TEXT); "
    "INSERT INTO c VALUES(10,1,'a'),(11,2,'b'),(12,2,'c');"
)
"""A parent with a column that the rebuild removes, and a child whose foreign key cascades."""
VIEWED_FAMILY = FAMILY + " CREATE VIEW pv AS SELECT id, name FROM p;"
"""The family with a view of the parent."""
REBUILD = (
    "BEGIN; CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT); INSERT INTO p_new SELECT id, name FROM p; "
    "DROP TABLE p; ALTER TABLE p_new RENAME TO p; COMMIT;"
)
"""The rebuild of the parent without its column `extra`, in one transaction."""
LOOK = " SELECT id,pid FROM c ORDER BY id; SELECT id,name FROM p ORDER BY id;"
"""The two tables, as they are afterwards."""


def definitions() -> list[QueryCase]:
    """The cases: the rebuild with the foreign-key settings, its variants and its failures."""
    def case(name: str, setup: str, sql: str, requirements: tuple[str, ...], *features: str) -> QueryCase:
        """Give a case its name prefix and features."""
        return QueryCase("rebuild-" + name, setup, sql, requirements, ("rebuild", *features))

    return [
        case("unsafe-cascade", FAMILY, REBUILD + LOOK + " PRAGMA foreign_key_check;", (IMPLICIT_DELETE, ACTIONS), "unsafe",
             "fk-on"),
        case("corrected", FAMILY, "BEGIN; "
             "CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT); INSERT INTO p_new SELECT id, name FROM p; "
             "DROP TABLE p; ALTER TABLE p_new RENAME TO p; PRAGMA foreign_key_check; COMMIT;" + LOOK,
             (CHECK,), "corrected"),
        case("corrected-finds-violation", FAMILY, "BEGIN; "
             "CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT); INSERT INTO p_new SELECT id, name FROM p WHERE id = 1; "
             "DROP TABLE p; ALTER TABLE p_new RENAME TO p; PRAGMA foreign_key_check; COMMIT;" + LOOK,
             (CHECK,), "corrected", "violation"),
        case("default-off", FAMILY, REBUILD + LOOK + " PRAGMA foreign_key_check;", (OFF_BY_DEFAULT,), "default"),
        case("pragma-in-transaction", FAMILY, "BEGIN; PRAGMA foreign_keys = OFF; "
             "PRAGMA foreign_keys; DROP TABLE p; COMMIT;" + " SELECT id,pid FROM c ORDER BY id;", (IN_TRANSACTION,),
             "pragma", "fk-on"),
        case("pragma-on-in-transaction", FAMILY, "BEGIN; PRAGMA foreign_keys = ON; PRAGMA foreign_keys; DROP TABLE p; "
             "COMMIT; SELECT id,pid FROM c ORDER BY id;", (IN_TRANSACTION,), "pragma"),
        case("rename-first", FAMILY, "BEGIN; ALTER TABLE p RENAME TO p_old; "
             "CREATE TABLE p(id INTEGER PRIMARY KEY, name TEXT); INSERT INTO p SELECT id, name FROM p_old; "
             "DROP TABLE p_old; COMMIT; SELECT \"table\" FROM pragma_foreign_key_list('c'); PRAGMA foreign_key_check;"
             + LOOK, (CHECK,), "rename-first", "fk-on"),
        case("drop-column-instead", FAMILY, "ALTER TABLE p DROP COLUMN extra;" + LOOK, (IMPLICIT_DELETE,), "drop-column",
             "fk-on"),
        case("view-blocks-rename", VIEWED_FAMILY, "BEGIN; CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT); INSERT INTO p_new SELECT id, name FROM p; "
             "DROP TABLE p; ALTER TABLE p_new RENAME TO p; COMMIT;" + LOOK, (CHECK,), "view", "prepare-error"),
        case("rollback", FAMILY, "BEGIN; CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT); "
             "INSERT INTO p_new SELECT id, name FROM p; DROP TABLE p; ALTER TABLE p_new RENAME TO p; ROLLBACK;" + LOOK
             + " SELECT * FROM p ORDER BY id;", (IMPLICIT_DELETE,), "rollback", "fk-on"),
        case("child-rebuild", FAMILY, "BEGIN; CREATE TABLE c_new(id INTEGER PRIMARY KEY, "
             "pid INTEGER REFERENCES p(id) ON DELETE CASCADE); INSERT INTO c_new SELECT id, pid FROM c; DROP TABLE c; "
             "ALTER TABLE c_new RENAME TO c; COMMIT; DELETE FROM p WHERE id = 2;" + LOOK, (ACTIONS,), "child", "fk-on"),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 7 record: a case with the feature `fk-on` under the measured profile
    with foreign keys on, any other case under SQLite's default measured profile. The migration runs on after an
    error."""
    selected = definitions() if cases is None else cases
    defaults, enforced = profile(()), foreign_key_profile()
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=enforced if "fk-on" in case.features else defaults, run_on=True, counters=True),
             "part": "rebuilds", "features": list(case.features)}
            for case in selected]
