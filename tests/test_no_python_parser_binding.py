"""No production Python module loads the SQLite parser library.

The text package's translation program (`packages/belay-sqlite-text`) is the only caller of the
parser library's C API (`parser/library.h`) outside its own tests; the harness reaches it through
`conformance/sql_text.py`. A Python binding would bring back a second path from SQL text to the
model's syntax, beside the one that the surface uses (ADR 0017, D6).
"""

from pathlib import Path

import pytest

pytestmark = [pytest.mark.unit]

ROOT = Path(__file__).resolve().parents[1]
PRODUCTION = ("belay", "conformance")
"""The folders of the production Python modules."""
LIBRARY_NAMES = ("sqlite-verifier-parser", "sqlite_verifier_parser_")
"""The parser library's file name and the prefix of its C functions, which a binding names."""
MINIMUM_PRODUCTION_MODULES = 50
"""Fewer modules than this mean that the search looked in the wrong folders and found nothing."""


def test_no_production_module_names_the_parser_library() -> None:
    """No Python file of `belay/` or `conformance/` names the library's file or its C functions."""
    modules = [path for folder in PRODUCTION for path in sorted((ROOT / folder).rglob("*.py"))]
    assert len(modules) > MINIMUM_PRODUCTION_MODULES
    found = [f"{path.relative_to(ROOT)}: {name}" for path in modules for name in LIBRARY_NAMES
             if name in path.read_text(encoding="utf-8")]
    assert found == []
