"""Authored cases of ADD COLUMN with REFERENCES and a default, under enforced foreign keys.

SQLite 3.51.0 refuses `ALTER TABLE ... ADD COLUMN ... REFERENCES ... DEFAULT x` on a nonempty
table while foreign keys are enforced, unless the last DEFAULT is the bare literal NULL
(`sqlite3AlterFinishAddColumn`). The cases cover the refusal, the empty table, the NULL default
and its position among several defaults, and the same column with enforcement turned off. They
are the targets of the mutants of `conformance.add_reference_mutants`. Native SQLite is the only
source of outcomes. The cases use `conformance.authored_queries.QueryCase`.
"""

from conformance import authored_foreign_keys, authored_resolution
from conformance.authored_queries import QueryCase
from conformance.case_format import Json
from conformance.native_record import record_sql

PARENT = "CREATE TABLE p(k PRIMARY KEY); INSERT INTO p VALUES(1), (99); CREATE TABLE c(a); "
"""A parent with the keys 1 and 99, and a child table without a foreign key."""
POPULATED = PARENT + "INSERT INTO c VALUES(5), (6);"
"""The child table with two rows."""
ADD_REFERENCE = "R-47952-62498"
"""SQLite: ALTER TABLE ADD COLUMN with a REFERENCES clause needs the default NULL (foreignkeys.html)."""
ADD_REFERENCE_ENFORCED = "R-13876-13274"
"""SQLite: with foreign keys enabled, a column added with a REFERENCES clause has the default NULL
(lang_altertable.html)."""
REQUIREMENTS = (ADD_REFERENCE, ADD_REFERENCE_ENFORCED)
"""The requirements that every case of this module covers."""
SHOW = " ALTER TABLE c ADD COLUMN z INTEGER DEFAULT 7; SELECT * FROM c;"
"""A control column after the statement under test, and the rows: they show whether the table is unchanged."""


def definitions() -> list[QueryCase]:
    """The cases of ADD COLUMN with REFERENCES: a refusal, an empty table, NULL defaults and no enforcement."""
    case = QueryCase
    return [
        case("add-reference-refused", POPULATED, "ALTER TABLE c ADD COLUMN y REFERENCES p(k) DEFAULT 99;" + SHOW,
             REQUIREMENTS, ("add-column", "references", "refused")),
        case("add-reference-empty", PARENT, "ALTER TABLE c ADD COLUMN y REFERENCES p(k) DEFAULT 99;" + SHOW,
             REQUIREMENTS, ("add-column", "references", "empty")),
        case("add-reference-null", POPULATED, "ALTER TABLE c ADD COLUMN y REFERENCES p(k) DEFAULT NULL;" + SHOW,
             REQUIREMENTS, ("add-column", "references", "null")),
        case("add-reference-last-default", POPULATED,
             "ALTER TABLE c ADD COLUMN y REFERENCES p(k) DEFAULT 99 DEFAULT NULL;"
             " ALTER TABLE c ADD COLUMN x REFERENCES p(k) DEFAULT NULL DEFAULT 99;" + SHOW,
             REQUIREMENTS, ("add-column", "references", "last-default")),
        case("add-reference-unenforced", POPULATED,
             "ALTER TABLE c ADD COLUMN y REFERENCES p(k) DEFAULT 99;" + SHOW,
             REQUIREMENTS, ("add-column", "references", "unenforced")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively with outputs, under the profile with foreign keys on of
    `conformance.authored_foreign_keys`, except the unenforced case, which runs under the
    default profile of `conformance.authored_resolution` with foreign keys off."""
    enforced, unenforced = authored_foreign_keys.profile(), authored_resolution.profile(())
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=unenforced if "unenforced" in case.features else enforced),
             "part": "add-references", "features": list(case.features)}
            for case in (definitions() if cases is None else cases)]
