"""Authored cases of the foreign-key atoms (task "foreign-key facts and preservation", ADR 0022 slice 5).

The cases are native regression evidence for the two accepted corrections of the task and for the
facts that its preservation laws rest on. `conformance.authored_add_references` and
`conformance.authored_foreign_key_defaults` cover the refusal to add a REFERENCES column with a non-NULL
default on a populated table while foreign keys are enforced, and the NOT NULL defaults. They also cover
the enforcement on and off. `conformance.authored_foreign_key_mapping` covers the NULL test and the
actions through the parent key columns that the engine selects, the actions beside RESTRICT, NO ACTION
and SET DEFAULT, and CREATE INDEX over a repeated column. Each record is a version 6 record
(`record_sql` with `run_on`), which runs on after an error. Native SQLite is the only source of outcomes.
"""

from conformance import authored_add_references, authored_foreign_key_defaults, authored_foreign_key_mapping
from conformance import authored_foreign_keys, authored_resolution
from conformance.authored_queries import QueryCase
from conformance.case_format import Json
from conformance.native_record import record_sql


def definitions() -> list[QueryCase]:
    """All cases of the foreign-key atoms, in the order of their modules."""
    return [*authored_add_references.definitions(), *authored_foreign_key_defaults.definitions(),
            *authored_foreign_key_mapping.definitions()]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 6 record in the part `foreign-key-atoms` with its features:
    under the profile with foreign keys on of `conformance.authored_foreign_keys`, or under SQLite's
    default measured profile for a case with the feature `unenforced`."""
    selected = definitions() if cases is None else cases
    enforced, unenforced = authored_foreign_keys.profile(), authored_resolution.profile(())
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=unenforced if "unenforced" in case.features else enforced, run_on=True),
             "part": "foreign-key-atoms", "features": list(case.features)}
            for case in selected]
