"""Refusals from Lean resolution reach the public `verify` result with their source range.

`migration_check/inputs.py` maps a resolver refusal (`Resolver.lean`) to a byte range
through the frontend's `Located` paths.
"""

from collections.abc import Callable
from pathlib import Path

import pytest

from tests.cli_test import approved, candidate, invoke  # noqa: F401  (pytest fixtures)

pytestmark = [pytest.mark.e2e, pytest.mark.kernel, pytest.mark.requires_lean,
              pytest.mark.requires_native]


@pytest.mark.parametrize("sql,refused", [
    ("CREATE INDEX i ON invoices(amount);", "CREATE INDEX i ON invoices(amount)"),
    ("CREATE TABLE t(a TEXT, rowid TEXT);", "a TEXT, rowid TEXT"),
    ("INSERT INTO invoices VALUES (1.5);", "1.5"),
], ids=["index_that_runs", "rowid_column", "real_value"])
def test_restriction_names_the_refused_sql(invoke: Callable[..., dict[str, object]], candidate: Path,
                                           sql: str, refused: str) -> None:
    """A model restriction from Lean resolution is UNSUPPORTED at the byte range of the refused node."""
    (candidate / "migration.sql").write_text(sql)
    report = invoke("UNSUPPORTED")
    start, end = report["start"], report["end"]
    assert isinstance(start, int) and isinstance(end, int)
    assert sql.encode()[start:end].decode() == refused, report
    assert str(report["source"]).endswith("migration.sql") and "; " in str(report["message"]), report


def test_schema_prepare_error_names_the_statement(invoke: Callable[..., dict[str, object]], approved: Path) -> None:
    """A schema statement that SQLite refuses is an input error with SQLite's message and its range."""
    schema = approved / "schema.sql"
    original = schema.read_bytes()
    schema.write_bytes(original + b"\nCREATE TABLE INVOICES(x);")
    report = invoke("INPUT_ERROR")
    assert "table INVOICES already exists" in str(report["message"]), report
    assert (original + b"\nCREATE TABLE INVOICES(x);")[report["start"]:report["end"]] == b"CREATE TABLE INVOICES(x)"
