"""The universal examples of fresh-run claims hold in the kernel with the conditions they state."""

import json
from pathlib import Path
import re
import shutil

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


def lines_after(stdout: str, tag: str) -> list[object]:
    """Decode the JSON that a fixture logged after the tag, one value for each line."""
    return [json.loads(line.removeprefix(tag)) for line in stdout.splitlines() if line.startswith(tag)]


def check_module_chain(runtime_root: Path, tmp_path: Path, modules: tuple[tuple[str, int], ...],
                       timeout: int = 120, output_of: str | None = None) -> str:
    """Elaborate the fixture modules in order, each importing the earlier ones, and audit the axioms of
    each module: its count of `#print axioms` reports is the given one, each report lists only ordinary
    logical axioms, and no proof is missing. The timeout, in seconds, applies to each module. It gives the
    output of the module named by `output_of`, or of the last module when none is named."""
    setup = module_setup(runtime_root, tmp_path)
    configuration = json.loads(setup.read_text())
    for module, count in modules:
        configuration["name"] = module
        setup.write_text(json.dumps(configuration))
        artifact = tmp_path / f"{module}.olean"
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                              "-R", str(FIXTURES), "-o", str(artifact),
                              str(FIXTURES / f"{module}.lean")], cwd=tmp_path, timeout=timeout)
        assert result.returncode == 0, result.diagnostic()
        reports = axiom_reports(result.stdout)
        assert len(reports) == count, result.diagnostic()
        for report in reports:
            assert report <= ALLOWED_PROOF_AXIOMS, result.diagnostic()
        assert "sorryAx" not in result.stdout, result.diagnostic()
        configuration["importArts"][module] = [[str(artifact)]]
        if module == output_of:
            chosen = result.stdout
    return result.stdout if output_of is None else chosen


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
    ordinary nullable UNIQUE constraint, which does not keep the invariant. The global form of the
    invariant (no email has two live accounts, a GROUP BY query) is proved for every admitted database
    with the same site and NOT NULL on the email, with the same counterexample."""
    check_module_chain(runtime_root, tmp_path, (
        ("AccountSignupQueries", 1), ("SignupInvariantClaims", 2), ("GlobalSignupInvariant", 3)))


@pytest.mark.requires_native("sqlite3")
def test_filtered_duplicate_key_query_agrees_with_native_sqlite(runtime_root: Path, tmp_path: Path) -> None:
    """The model's result of the guide's global signup invariant query (our filtered duplicate-key
    query law and `Holds`) agrees with pinned native SQLite on six databases: no live duplicate, a live
    duplicate, a duplicate with one deleted account, two live NULL emails (GROUP BY joins NULL keys), and
    emails that are equal only under NOCASE, with and without that collation in GROUP BY. The kernel checks the
    same results in the fixture; the fixture logs the SQL and the model's result of each case."""
    stdout = check_module_chain(runtime_root, tmp_path, (
        ("AccountSignupQueries", 1), ("SignupInvariantClaims", 2), ("GlobalSignupInvariant", 3),
        ("FilteredDuplicateKeyExamples", 1)))
    cases = {str(case["name"]): case for case in lines_after(stdout, "FILTERED-DUPLICATES:")
             if isinstance(case, dict)}
    assert set(cases) == {"noLiveDuplicate", "liveDuplicate", "deletedDuplicate", "nullKeys", "nocaseBinary",
                          "nocaseNocase"}, stdout
    assert {name: case["holds"] for name, case in cases.items()} == {
        "noLiveDuplicate": True, "liveDuplicate": False, "deletedDuplicate": True, "nullKeys": False,
        "nocaseBinary": True, "nocaseNocase": False}
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    for name, case in cases.items():
        script = tmp_path / f"{name}.sql"
        script.write_text(f"{case['setup']};\n{case['query']};\n")
        native = run_command([sqlite, "-batch", "-bail", "-json", ":memory:", f'.read "{script}"'],
                             cwd=tmp_path, timeout=10)
        assert native.returncode == 0 and not native.stderr, native.diagnostic()
        rows = json.loads(native.stdout) if native.stdout.strip() else []
        assert [list(row.values()) for row in rows] == ([[1]] if case["holds"] else []), (name, native.stdout)


def test_two_state_assertions_follow_the_start_and_the_reached_database(runtime_root: Path, tmp_path: Path) -> None:
    """A source that names `before` reads the initial database that the assertion is given, a plain source
    reads the reached database, and a query with no `before` source is the one-state assertion whatever the
    start is. The default and the real-context observation differ on a clock, a compound EXCEPT compares the
    start with the reached rows, and the `ensuresFrom` notation is the primitive claim."""
    check_module_chain(runtime_root, tmp_path, (("TwoStateAssertionExamples", 10),))


def test_delete_trigger_removes_an_unrelated_row(runtime_root: Path, tmp_path: Path) -> None:
    """A delete trigger may remove a row of another customer: the kernel confirms, from the actual run of
    the delete, that a session of another customer exists before and is gone after the successful
    delete, and that the same run without the trigger keeps it."""
    check_module_chain(runtime_root, tmp_path, (("PurgeTriggerCounterexample", 2),))


def test_added_customer_claim_over_every_database(runtime_root: Path, tmp_path: Path) -> None:
    """The guide's claim about the program that uses a result is proved for every admitted database with
    the stated site (schema, resolution without rules, affinities, and a modeled query and insert for every
    value that the query returns), every name and email: when the program reports success, a customer with
    the name exists. The fixture shows the site on a database, where the kernel runs the program and finds
    the customer, and keeps the counterexample that the site excludes: a trigger that removes the new
    customer after a successful insert. The instance module needs a longer timeout than the others,
    because the kernel evaluates the model's run of the insert for every environment (about 40 s)."""
    check_module_chain(runtime_root, tmp_path, (
        ("AddCustomerQueries", 0), ("AddCustomerClaims", 1), ("AddCustomerInstances", 2)), timeout=300)


def test_purge_frame_claim_over_every_database(runtime_root: Path, tmp_path: Path) -> None:
    """The guide's purge frame claim is proved for every admitted database with the stated site (the
    schema with a rowid alias, the resolution of the purge as a plain delete and of the claim as a compound
    EXCEPT against `before`, and a modeled purge), for every pair of values, NULL and text included: a purge
    that succeeds leaves every session that is not an expired session of the customer. The condition is
    the NULL-aware `IS NOT 1`. The fixture shows the site and the actual run for NULL parameters, for a text
    time that deletes every session of the customer, and for an integer time; it keeps the counterexamples
    that the claim and its form exclude: the variant of the purge with OR for AND, the claim with NOT
    instead of IS NOT 1 that requires nothing for a NULL parameter, and an aborted purge whose rollback
    leaves the start."""
    check_module_chain(runtime_root, tmp_path, (
        ("PurgeFrameQueries", 4), ("PurgeFrameSite", 0), ("PurgeFrameClaims", 2), ("PurgeFrameInstances", 12)),
        timeout=300)
