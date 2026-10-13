"""The help text of the authored corpus writers (`conformance.query_evidence` and
`conformance.number_evidence`).

A user runs these commands to create a coverage corpus; their help text must say
what the command does in plain words, without internal document references such as
ADR numbers (CLAUDE.md, error messages and user-facing text).
"""

import sys
from pathlib import Path

import pytest

from tests.runtime_support import run_command

pytestmark = [pytest.mark.unit]
ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize(("module", "subject"), [("conformance.query_evidence", "query"),
                                                 ("conformance.number_evidence", "number")])
def test_help_describes_corpus_creation_without_document_references(module: str, subject: str) -> None:
    """`--help` succeeds, names the cases and the new corpus directory, and mentions no ADR."""
    result = run_command([sys.executable, "-m", module, "--help"], cwd=ROOT, timeout=30)
    assert result.returncode == 0, result.diagnostic()
    text = " ".join(result.stdout.split())
    assert f"authored {subject} cases" in text and "new corpus directory" in text and "--output" in text
    assert "ADR" not in text
