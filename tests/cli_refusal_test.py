"""Refusals from Lean resolution reach the public `verify` result with their source range.

`migration_check/inputs.py` maps a resolver refusal (`packages/verifier-gate/Resolver.lean`)
to a byte range through the frontend's `Located` paths.
"""

from collections.abc import Callable
from pathlib import Path

import pytest

from tests.cli_test import approved, candidate, invoke  # noqa: F401  (pytest fixtures)

pytestmark = [pytest.mark.e2e, pytest.mark.kernel, pytest.mark.requires_lean,
              pytest.mark.requires_native]


@pytest.mark.parametrize("sql,refused,restriction", [
    ("CREATE INDEX i ON invoices(json_extract(amount, '$'));", "json_extract(amount, '$')", "index-json-function"),
    ("CREATE TABLE t(a TEXT, rowid TEXT);", "a TEXT, rowid TEXT", "rowid-column-name"),
    ("SELECT amount FROM invoices WHERE rowid = 1;", "rowid", "rowid-name"),
], ids=["index_json_function", "rowid_column", "rowid_name"])
def test_restriction_names_the_refused_sql(invoke: Callable[..., dict[str, object]], candidate: Path,
                                           sql: str, refused: str, restriction: str) -> None:
    """A model restriction from Lean resolution is UNSUPPORTED at the byte range of the refused node,
    and the report names the restriction's stable id from the registry (`RestrictionKind.id`)."""
    (candidate / "migration.sql").write_text(sql)
    report = invoke("UNSUPPORTED")
    start, end = report["start"], report["end"]
    assert isinstance(start, int) and isinstance(end, int)
    assert sql.encode()[start:end].decode() == refused, report
    assert str(report["source"]).endswith("migration.sql") and "; " in str(report["message"]), report
    assert report["restriction"] == restriction, report


def test_schema_prepare_error_names_the_statement(invoke: Callable[..., dict[str, object]], approved: Path) -> None:
    """A schema statement that SQLite refuses is an input error with SQLite's message and its range."""
    schema = approved / "schema.sql"
    original = schema.read_bytes()
    schema.write_bytes(original + b"\nCREATE TABLE INVOICES(x);")
    report = invoke("INPUT_ERROR")
    assert "table INVOICES already exists" in str(report["message"]), report
    assert (original + b"\nCREATE TABLE INVOICES(x);")[report["start"]:report["end"]] == b"CREATE TABLE INVOICES(x)"
