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


def test_signup_invariant_with_partial_unique_index(runtime_root: Path, tmp_path: Path) -> None:
    """The guide's signup invariant is proved for every admitted database with a site of the signup
    insert and the partial unique index on the email of the live accounts: for every email value, a run
    that succeeds keeps at most one live account with that email. The fixture shows the invariant kept on
    a database for a new email, a rejected live email whose rolled-back database still satisfies the
    invariant, and a deleted account whose email can be reused, and keeps the counterexample of an
    ordinary nullable UNIQUE constraint, which does not keep the invariant."""
    check_module_chain(runtime_root, tmp_path, (("AccountSignupQueries", 1), ("SignupInvariantClaims", 2)))


def test_delete_trigger_removes_an_unrelated_row(runtime_root: Path, tmp_path: Path) -> None:
    """A delete trigger may remove a row of another customer: the kernel confirms, from the actual run of
    the delete, that a session of another customer exists before and is gone after the successful
    delete, and that the same run without the trigger keeps it."""
    check_module_chain(runtime_root, tmp_path, (("PurgeTriggerCounterexample", 2),))
