"""Check the offline report's actual graph algorithms and safe data embedding."""

from html.parser import HTMLParser
import json
from pathlib import Path
import subprocess

import pytest

from tools.theorem_dependency_report import write_report

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [pytest.mark.unit]


class ScriptReader(HTMLParser):
    """Extract inert report data and detect scripts introduced by embedded source text."""

    def __init__(self) -> None:
        """Record script tags separately from the JSON payload."""
        super().__init__()
        self.script_count = 0
        self.in_data = False
        self.payload = ""

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        """Identify the data script while counting all executable script elements."""
        if tag == "script":
            self.script_count += 1
            self.in_data = dict(attrs).get("id") == "graph-data"

    def handle_endtag(self, tag: str) -> None:
        """Stop collecting JSON at the inert script's closing tag."""
        if tag == "script":
            self.in_data = False

    def handle_data(self, data: str) -> None:
        """Retain exact JSON text for the round-trip check."""
        if self.in_data:
            self.payload += data


def test_graph_paths_helpers_cycles_and_candidates() -> None:
    """The report's JavaScript keeps hidden proof paths, edge filters and cycles correct."""
    result = subprocess.run(["node", str(ROOT / "tests/theorem_dependency_graph_test.js")],
                            cwd=ROOT, text=True, capture_output=True, timeout=10, check=False)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "graph checks passed" in result.stdout


def test_report_embeds_source_and_names_as_data(tmp_path: Path) -> None:
    """Report data cannot terminate its script, and offline assets preserve Unicode and source."""
    hostile = '</script><script>alert("source")</script>α&\u2028'
    data: dict[str, object] = {
        "schemaVersion": 1, "leanVersion": "4.34.1", "external": [],
        "modules": [{"name": "Fixture", "source": "Fixture.lean", "sourceText": hostile}],
        "declarations": [{"name": hostile, "module": "Fixture", "kind": "theorem",
                          "typeReferences": [], "bodyReferences": [], "selection": [0, 0, 0, 1]}],
    }
    output = tmp_path / "nested/index.html"
    write_report(data, output)
    document = output.read_text(encoding="utf-8")
    parser = ScriptReader()
    parser.feed(document)
    assert parser.script_count == 4
    assert json.loads(parser.payload) == data
    assert "<!-- graph-data -->" not in document
    assert "<!-- graph.js -->" not in document
    assert "innerHTML" not in document
    assert "function dependencyPath" in document
    assert 'src="http' not in document


def test_report_rejects_incompatible_schema(tmp_path: Path) -> None:
    """The report writer rejects incompatible input before writing a misleading artifact."""
    with pytest.raises(ValueError, match="schemaVersion"):
        write_report({"schemaVersion": 2}, tmp_path / "index.html")
    with pytest.raises(ValueError, match="declarations must be a list"):
        write_report({"schemaVersion": 1, "modules": [], "declarations": {}}, tmp_path / "index.html")
    assert not (tmp_path / "index.html").exists()
