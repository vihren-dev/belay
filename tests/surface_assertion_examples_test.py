"""The universal examples of fresh-run claims hold in the kernel with the conditions they state."""

import json
from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

ALLOWED_PROOF_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
"""Ordinary logical axioms; unchecked evaluation and assumed execution soundness are excluded."""

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def axiom_reports(stdout: str) -> list[set[str]]:
    """The axiom sets of all `#print axioms` reports in the output of one Lean run."""
    reports = re.findall(r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", stdout)
    return [set(filter(None, map(str.strip, report.split(",")))) for report in reports]


def check_module_chain(runtime_root: Path, tmp_path: Path, modules: tuple[tuple[str, int], ...]) -> None:
    """Elaborate the fixture modules in order, each importing the earlier ones, and audit the axioms of
    each module: its count of `#print axioms` reports is the given one, each report lists only ordinary
    logical axioms, and no proof is missing."""
    setup = module_setup(runtime_root, tmp_path)
    configuration = json.loads(setup.read_text())
    for module, count in modules:
        configuration["name"] = module
        setup.write_text(json.dumps(configuration))
        artifact = tmp_path / f"{module}.olean"
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                              "-R", str(FIXTURES), "-o", str(artifact),
                              str(FIXTURES / f"{module}.lean")], cwd=tmp_path, timeout=120)
        assert result.returncode == 0, result.diagnostic()
        reports = axiom_reports(result.stdout)
        assert len(reports) == count, result.diagnostic()
        for report in reports:
            assert report <= ALLOWED_PROOF_AXIOMS, result.diagnostic()
        assert "sorryAx" not in result.stdout, result.diagnostic()
        configuration["importArts"][module] = [[str(artifact)]]


def test_insert_then_lookup_claims_over_every_database(runtime_root: Path, tmp_path: Path) -> None:
    """The guide's insert and lookup claim is proved for every admitted database with the stated site of
    the insert (schema, resolution without rules, affinities, and a modeled statement), every id and every
    name. The fixture shows that the site and the guard are satisfiable on a database, and keeps the
    counterexamples that the conditions exclude: a trigger that removes the inserted row, the missing
    guard on a table without a key, and a duplicate name that fails the insert. Every instance and
    counterexample is checked from the actual run of the statement."""
    check_module_chain(runtime_root, tmp_path, (
        ("CustomerInsertSite", 2), ("CustomerInsertQueries", 5), ("InsertLookupClaims", 3)))


def test_preserved_count_claim_over_every_database(runtime_root: Path, tmp_path: Path) -> None:
    """The guide's preserved-count claim is proved for every admitted database with a site of the
    lowercase-field expansion, every count, every pair of triggers and every bound values, under the
    condition that the expansion runs without an error. The fixture shows that the site and the condition
    are satisfiable on a database, and keeps the counterexample that the site excludes: a trigger on UPDATE
    that existed before the expansion and removes the rows when the backfill fires it."""
    check_module_chain(runtime_root, tmp_path, (("ExpansionCountQueries", 1), ("ExpansionCountClaims", 3)))
