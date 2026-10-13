"""Authored coverage cases of the first-scope name-resolution rules (ADR 0008).

The coverage rule of ADR 0008 ("How `resolve` is tested") asks, for each condition
of each rule, for a case where the condition applies, a neighbor where it just does
not apply, and cases where two errors apply at once, so that the corpus records
which error SQLite reports. Native SQLite is the only source of outcomes: these are
inputs, recorded as version 5 records with the error phase of each statement.
Column-limit cases run under a profile whose column limit is lowered to 5.
"""

from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory

from conformance.case_format import Json
from conformance.execution_profile import ExecutionProfile, measured_profile
from conformance.native_connection import Connection, library_path, load_library
from conformance.native_limits import lower_limits
from conformance.native_record import record_sql

TABLE = "CREATE TABLE t(a INTEGER, b TEXT); CREATE INDEX t_b ON t(b); INSERT INTO t VALUES(1, 'x');"
"""The starting schema of most cases: one table with a row and an index."""
NARROW = "CREATE TABLE n(c0, c1, c2, c3);"
"""A table one column below the lowered limit of 5."""
LOWERED = (("columns", 5),)
"""The lowered limits of the column-limit cases."""


@dataclass(frozen=True)
class ResolutionCase:
    """One coverage case: setup and migration SQL, the requirement identifiers it covers,
    descriptive features, and the connection limits it lowers."""

    name: str
    setup: str
    sql: str
    requirements: tuple[str, ...]
    features: tuple[str, ...]
    limits: tuple[tuple[str, int], ...] = ()


def definitions() -> list[ResolutionCase]:
    """The coverage cases: each condition, its neighbor, and two errors at once."""
    case = ResolutionCase
    return [
        case("reserved-name", TABLE, "CREATE TABLE sqlite_x(a);", ("R-17899-04554",), ("create-table", "reserved-name")),
        case("reserved-name-neighbor", TABLE, "CREATE TABLE sqlitex(a);", ("R-17899-04554",), ("create-table", "neighbor")),
        case("table-exists", TABLE, "CREATE TABLE t(c);", ("R-01232-54838",), ("create-table", "table-exists")),
        case("table-exists-folded", TABLE, "CREATE TABLE T(c);", ("R-01232-54838", "R-23648-58527"),
             ("create-table", "table-exists", "ascii-folding")),
        case("table-exists-non-ascii-neighbor", "CREATE TABLE ét(a);", "CREATE TABLE ÉT(a);", ("R-23648-58527",),
             ("create-table", "ascii-folding", "neighbor")),
        case("index-name-used", TABLE, "CREATE TABLE t_b(c);", ("R-01232-54838",), ("create-table", "index-name")),
        case("duplicate-column-create", TABLE, "CREATE TABLE u(a, A);", ("R-01232-54838",),
             ("create-table", "duplicate-column", "ascii-folding")),
        case("duplicate-column-create-neighbor", TABLE, "CREATE TABLE u(a, b);", ("R-01232-54838",),
             ("create-table", "neighbor")),
        case("too-many-columns-create", TABLE, "CREATE TABLE u(c0, c1, c2, c3, c4, c5);", ("R-25473-20557", "R-27775-64721"),
             ("create-table", "column-limit"), LOWERED),
        case("too-many-columns-create-neighbor", TABLE, "CREATE TABLE u(c0, c1, c2, c3, c4);",
             ("R-25473-20557", "R-27775-64721"), ("create-table", "column-limit", "neighbor"), LOWERED),
        case("multiple-primary-keys", TABLE, "CREATE TABLE u(a PRIMARY KEY, b PRIMARY KEY);", ("R-31826-01813",),
             ("create-table", "primary-key")),
        case("multiple-primary-keys-neighbor", TABLE, "CREATE TABLE u(a PRIMARY KEY, b);", ("R-31826-01813",),
             ("create-table", "primary-key", "neighbor")),
        case("nonconstant-default", TABLE, "CREATE TABLE u(a, b DEFAULT (a));", ("R-07343-35026",),
             ("create-table", "default")),
        case("nonconstant-default-neighbor", TABLE, "CREATE TABLE u(a, b DEFAULT 1);", ("R-07343-35026",),
             ("create-table", "default", "neighbor")),
        case("add-missing-table", TABLE, "ALTER TABLE missing ADD c;", ("R-10948-48115",), ("add-column", "missing-table")),
        case("add-duplicate-column", TABLE, "ALTER TABLE t ADD A;", ("R-10948-48115", "R-23648-58527"),
             ("add-column", "duplicate-column", "ascii-folding")),
        case("add-duplicate-column-neighbor", TABLE, "ALTER TABLE t ADD c;", ("R-10948-48115",), ("add-column", "neighbor")),
        case("add-too-many-columns", NARROW + "ALTER TABLE n ADD c4;", "ALTER TABLE n ADD c5;",
             ("R-25473-20557", "R-27775-64721"), ("add-column", "column-limit"), LOWERED),
        case("add-reaches-column-limit", NARROW, "ALTER TABLE n ADD c4;", ("R-25473-20557", "R-27775-64721"),
             ("add-column", "column-limit", "neighbor"), LOWERED),
        case("add-limit-before-duplicate", NARROW + "ALTER TABLE n ADD c4;", "ALTER TABLE n ADD c0;",
             ("R-25473-20557", "R-27775-64721"), ("add-column", "column-limit", "two-errors"), LOWERED),
        case("add-schema-table", TABLE, "ALTER TABLE sqlite_schema ADD c;", ("R-17899-04554", "R-10948-48115"),
             ("add-column", "reserved-name")),
        case("add-not-null-to-rows", TABLE, "ALTER TABLE t ADD c NOT NULL;", ("R-29868-13536",),
             ("add-column", "not-null", "step-error")),
        case("add-primary-key", TABLE, "ALTER TABLE t ADD c PRIMARY KEY;", ("R-45735-05060",), ("add-column", "primary-key")),
        case("add-plain-column-neighbor", TABLE, "ALTER TABLE t ADD c INTEGER;", ("R-45735-05060",),
             ("add-column", "neighbor")),
        case("insert-missing-table", TABLE, "INSERT INTO missing VALUES(1);", ("R-07016-26442",), ("insert", "missing-table")),
        case("insert-missing-column", TABLE, "INSERT INTO t(missing) VALUES(1);", ("R-07016-26442",),
             ("insert", "missing-column")),
        case("insert-named-column-neighbor", TABLE, "INSERT INTO t(a) VALUES(2);", ("R-07016-26442",),
             ("insert", "neighbor")),
        case("insert-value-count", TABLE, "INSERT INTO t VALUES(1, 'y', 3);", ("R-19218-01018",), ("insert", "value-count")),
        case("insert-value-count-neighbor", TABLE, "INSERT INTO t VALUES(2, 'y');", ("R-19218-01018",),
             ("insert", "neighbor")),
        case("insert-values-for-columns", TABLE, "INSERT INTO t(a) VALUES(2, 'y');", ("R-21115-58321",),
             ("insert", "value-count")),
        case("insert-rows-differ", TABLE, "INSERT INTO t(a, b) VALUES(2, 'y'), (3);", ("R-21115-58321",),
             ("insert", "value-count")),
        case("insert-rows-match-neighbor", TABLE, "INSERT INTO t(a, b) VALUES(2, 'y'), (3, 'z');", ("R-21115-58321",),
             ("insert", "neighbor")),
        case("insert-missing-table-and-count", TABLE, "INSERT INTO missing(a) VALUES(1, 2);", ("R-07016-26442",),
             ("insert", "missing-table", "two-errors")),
        case("update-missing-table", TABLE, "UPDATE missing SET a = 1;", ("R-40598-36595",), ("update", "missing-table")),
        case("update-missing-column", TABLE, "UPDATE t SET missing = 1;", ("R-40598-36595",), ("update", "missing-column")),
        case("update-missing-filter-column", TABLE, "UPDATE t SET a = 2 WHERE missing = 1;", ("R-40598-36595",),
             ("update", "missing-column")),
        case("update-neighbor", TABLE, "UPDATE t SET a = 2 WHERE a = 1;", ("R-40598-36595",), ("update", "neighbor")),
        case("commit-without-transaction", TABLE, "COMMIT;", ("R-42089-41020",), ("transaction", "step-error")),
        case("rollback-without-transaction", TABLE, "ROLLBACK;", ("R-42089-41020",), ("transaction", "step-error")),
        case("begin-within-transaction", TABLE, "BEGIN; BEGIN;", ("R-11576-11990", "R-02854-44844"),
             ("transaction", "step-error")),
        case("begin-commit-neighbor", TABLE, "BEGIN; ALTER TABLE t ADD c; COMMIT;", ("R-36570-50350",),
             ("transaction", "neighbor")),
    ]


def profile(limits: tuple[tuple[str, int], ...]) -> ExecutionProfile:
    """A measured profile of format 3 with SQLite's default execution settings and the given
    lowered limits."""
    with TemporaryDirectory(prefix="resolution-profile-") as directory:
        connection = Connection(load_library(library_path()), Path(directory) / "measure.db")
        try:
            lower_limits(connection, dict(limits))
            name = "resolution-default-v1" if not limits else "resolution-" + "-".join(
                f"{key}-{value}" for key, value in limits) + "-v1"
            return measured_profile(connection, name=name, format_version=3)
        finally:
            connection.close()


def records(cases: list[ResolutionCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record, with its part and features."""
    selected = definitions() if cases is None else cases
    profiles = {limits: profile(limits) for limits in {case.limits for case in selected}}
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements),
                          outputs=True, profile=profiles[case.limits]),
             "part": "resolution", "features": list(case.features)}
            for case in selected]
