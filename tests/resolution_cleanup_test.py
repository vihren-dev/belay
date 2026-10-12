"""The cleanup conditions of ADR 0008 hold: resolution lives only in Lean.

These checks read this repository's source text. They find a frontend module that
does resolution work again, or a file that still uses a replaced Lean name. They
do not check behavior; the Lean proofs, examples and the conformance suite do.
"""

from pathlib import Path
import re

import pytest

ROOT = Path(__file__).resolve().parents[1]
FRONTEND = ROOT / "belay/sqlite"
pytestmark = [pytest.mark.unit]

FRONTEND_PATTERNS = {
    "case folding": re.compile(r"maketrans|\.lower\(|\.upper\(|casefold"),
    "affinity rule": re.compile(r"[Aa]ffinity"),
    "column limit": re.compile(r"\b2,?000\b"),
    "schema or catalog type": re.compile(r"\b(class|import)\s+\w*(Table|Schema|Catalog|Column)\b"),
}
"""Resolution work that ADR 0008 removes from the frontend, by kind."""

REPLACED_NAMES = re.compile(r"DeclaredType|maximumColumns|\.sqlite351|\.sqlite346")
"""Lean names that ADR 0008 replaced; no Lean or Python source may use them."""

RECORDS = ("reports", "plans", "reviews", "docs", "build", ".lake", "conformance/corpus")
"""Historical records and outputs, which keep the names they had."""

ABSENCE_CHECKS = ("tests/shared_table_shape_test.py",)
"""Tests that name the replaced names to check that the compiler refuses them."""


def sources(*suffixes: str) -> list[Path]:
    """Every source file with the suffixes, outside historical records and this test."""
    found = []
    for suffix in suffixes:
        for path in ROOT.rglob(f"*{suffix}"):
            relative = path.relative_to(ROOT).as_posix()
            if (not relative.startswith(RECORDS) and "/.lake/" not in relative and path != Path(__file__)
                    and relative not in ABSENCE_CHECKS):
                found.append(path)
    return found


@pytest.mark.parametrize("kind", FRONTEND_PATTERNS)
def test_frontend_does_no_resolution(kind: str) -> None:
    """No frontend module folds case, applies affinity rules, knows the column limit or holds a schema type."""
    matches = [f"{path.relative_to(ROOT)}:{number}" for path in sorted(FRONTEND.glob("*.py"))
               for number, line in enumerate(path.read_text().splitlines(), 1) if FRONTEND_PATTERNS[kind].search(line)]
    assert not matches, f"{kind} in the frontend: {matches}"


def test_replaced_lean_names_are_unused() -> None:
    """No Lean or Python source outside historical records uses a name that ADR 0008 replaced."""
    matches = [f"{path.relative_to(ROOT)}:{number}" for path in sources(".lean", ".py")
               for number, line in enumerate(path.read_text(errors="replace").splitlines(), 1)
               if REPLACED_NAMES.search(line)]
    assert not matches, f"replaced names in use: {matches}"
