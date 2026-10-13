"""`migration_check.cli.main`: the human-readable output of successful commands."""

import argparse

import pytest

from migration_check import cli, prepare

pytestmark = pytest.mark.unit

PREPARE_ARGUMENTS = ["prepare", "--profile", "3.51.0", "--schema", "s", "--requirements", "r",
                     "--interpretation", "i", "--migration", "m", "--project", "p", "--output", "proof.bundle"]
"""A complete `prepare` command line; the command itself is replaced below."""


def test_prepare_prints_warnings_before_the_result(monkeypatch: pytest.MonkeyPatch,
                                                  capsys: pytest.CaptureFixture[str]) -> None:
    """`main` prints each `prepare` warning on its own `warning:` line, then `PREPARED`, and exits 0, so a
    person running `prepare` sees the warning without JSON output."""
    def prepared(_options: argparse.Namespace) -> dict[str, object]:
        """A successful preparation with one warning."""
        return {"status": "PREPARED", "bundle": "proof.bundle", "compiled_modules": [],
                "warnings": ["Requirements:3: #eval runs code"]}
    monkeypatch.setattr(prepare, "prepare", prepared)
    assert cli.main(PREPARE_ARGUMENTS) == 0
    assert capsys.readouterr().out.splitlines() == ["warning: Requirements:3: #eval runs code",
                                                    "PREPARED: proof.bundle"]


def test_rejection_details_join_the_report() -> None:
    """`Rejection.diagnostic` adds its details, such as `compiled_modules`, to the report of a refutation, while
    the status and message stay the rejection's own."""
    from migration_check.diagnostics import Rejection

    report = Rejection("VIOLATED", "refuted", details={"compiled_modules": [], "status": "VERIFIED"}).diagnostic()
    assert report["status"] == "VIOLATED" and report["message"] == "refuted" and report["compiled_modules"] == []
