"""Measured connection limits and error phases of the native recorder (ADR 0008).

`conformance.native_limits` measures and lowers the limits of a connection;
`conformance.execution_profile` records them in profile format 3 and derives them
from the compile options of an older profile; `conformance.native_connection`
reports whether a statement failed in `sqlite3_prepare_v2` or in `sqlite3_step`.
"""

from dataclasses import replace
from pathlib import Path

import pytest

from conformance.execution_profile import measured_profile, profile_from_wire
from conformance.native_connection import Connection, NativeError, library_path, load_library
from conformance.native_limits import LIMIT_IDS, compile_option_limits, lower_limits, measured_limits

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_native("sqlite3")]
DOCUMENTED = {name: default for name, (_, _, default) in LIMIT_IDS.items()}
"""SQLite's documented defaults, which the pinned build keeps."""


@pytest.fixture
def connection(tmp_path: Path) -> Connection:
    """One fresh connection to the pinned library."""
    opened = Connection(load_library(library_path()), tmp_path / "limits.db")
    yield opened
    opened.close()


def test_connection_keeps_and_reports_the_compile_time_limits(connection: Connection) -> None:
    """A new connection applies no limit of its own: it reports the build's compile-time values."""
    assert measured_limits(connection) == DOCUMENTED


def test_lowered_column_limit_is_measured_and_enforced(connection: Connection) -> None:
    """A lowered column limit is the measured value, and SQLite enforces it. The limit
    is 5 because SQLite's own `sqlite_schema` table has 5 columns: below that, SQLite
    cannot read the schema."""
    assert lower_limits(connection, {"columns": 5}) == {**DOCUMENTED, "columns": 5}
    connection.execute_script("CREATE TABLE t(a, b, c, d, e);")
    with pytest.raises(NativeError, match="too many columns"):
        connection.query("ALTER TABLE t ADD d;")


@pytest.mark.parametrize("request_", [{"columns": 2001}, {"unknown": 1}, {"columns": -1}])
def test_limit_requests_above_the_build_or_unknown_are_refused(connection: Connection,
                                                               request_: dict[str, int]) -> None:
    """SQLite caps a higher value silently, so the recorder refuses it instead of recording a cap."""
    with pytest.raises(ValueError, match="Cannot lower the native limit"):
        lower_limits(connection, request_)


def test_profile_records_and_reestablishes_its_limits(connection: Connection, tmp_path: Path) -> None:
    """Format 3 records the measured limits, round-trips them, and establishes them on a new connection."""
    lower_limits(connection, {"columns": 5, "length": 100})
    profile = measured_profile(connection, name="lowered", format_version=3)
    assert profile.effective_limits() == {**DOCUMENTED, "columns": 5, "length": 100}
    assert profile_from_wire(profile.to_wire()) == profile
    other = Connection(load_library(library_path()), tmp_path / "other.db")
    try:
        profile.establish(other)
        assert measured_limits(other) == profile.effective_limits()
    finally:
        other.close()
    with pytest.raises(ValueError, match="execution profile"):
        profile_from_wire({**profile.to_wire(), "limits": {"columns": 5}})


def test_older_profile_takes_its_limits_from_compile_options(connection: Connection) -> None:
    """A profile without a limits field gets the `SQLITE_MAX_*` values of its compile options."""
    profile = measured_profile(connection, name="old", format_version=2)
    assert "limits" not in profile.to_wire()
    assert profile.effective_limits() == DOCUMENTED
    assert compile_option_limits(("MAX_COLUMN=7", "THREADSAFE=1")) == {**DOCUMENTED, "columns": 7}
    with pytest.raises(ValueError, match="execution profile"):
        replace(profile, limits=(("columns", 5),))


def test_error_phase_names_the_failing_call(connection: Connection) -> None:
    """A missing table fails in `sqlite3_prepare_v2`; a constraint violation fails in `sqlite3_step`."""
    connection.execute_script("CREATE TABLE t(id INTEGER NOT NULL);")
    with pytest.raises(NativeError) as prepared:
        connection.query("INSERT INTO missing VALUES(1);")
    with pytest.raises(NativeError) as stepped:
        connection.query("INSERT INTO t VALUES(NULL);")
    assert (prepared.value.phase, prepared.value.code & 255) == ("prepare", 1)
    assert (stepped.value.phase, stepped.value.code & 255) == ("step", 19)
