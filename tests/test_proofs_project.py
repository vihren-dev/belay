"""`migration_check.proofs_project`: the parts of the user's proofs project that the tool owns or checks."""

import os
from pathlib import Path
import tomllib

import pytest

from migration_check.proofs_project import (RUNTIME_LINK, check_disabling_settings, link_runtime, missing_modules,
                                            project_lakefile, reads_contract_from, write_generated)

pytestmark = pytest.mark.unit


def test_link_points_at_the_installation_and_follows_a_new_one(tmp_path: Path) -> None:
    """`link_runtime` creates `.belay/runtime` and replaces it when the installation changes, so a portable
    lakefile can require the library through it."""
    first, second = tmp_path / "first", tmp_path / "second"
    first.mkdir()
    second.mkdir()
    project = tmp_path / "project"
    project.mkdir()
    link_runtime(project, first)
    link_runtime(project, first)
    assert Path(os.readlink(project / RUNTIME_LINK)) == first
    link_runtime(project, second)
    assert Path(os.readlink(project / RUNTIME_LINK)) == second


def test_generation_writes_only_changed_modules(tmp_path: Path) -> None:
    """`write_generated` leaves an unchanged file alone (same modification time), so generating again never
    makes Lake rebuild."""
    assert write_generated(tmp_path, {"SchemaInputs": "a", "SqlInputs": "b"}) == ["SchemaInputs", "SqlInputs"]
    before = (tmp_path / "Generated/SchemaInputs.lean").stat().st_mtime_ns
    assert write_generated(tmp_path, {"SchemaInputs": "a", "SqlInputs": "c"}) == ["SqlInputs"]
    assert (tmp_path / "Generated/SchemaInputs.lean").stat().st_mtime_ns == before


def test_starting_lakefile_reads_contract_in_place_and_requires_the_link() -> None:
    """`project_lakefile` declares the contract with its folder as `srcDir`, the generated modules, the
    candidate modules, and the audit module outside the default targets, and requires the library through
    `.belay/runtime`."""
    parsed = tomllib.loads(project_lakefile("proofs", "../approved", ["Requirements", "Interpretation"],
                                            ["NextInterpretation", "Proofs"]))
    assert parsed["require"] == [{"name": "sqliteVerifier", "path": ".belay/runtime"}]
    assert [(lib["name"], lib["srcDir"]) for lib in parsed["lean_lib"]] == [
        ("Contract", "../approved"), ("GeneratedInputs", "Generated"), ("Candidate", "."), ("Audit", "Generated")]
    assert parsed["defaultTargets"] == ["Contract", "GeneratedInputs", "Candidate"]
    assert parsed["lean_lib"][3]["roots"] == ["Check"]
    assert parsed["lean_lib"][1]["roots"] == ["SchemaInputs", "SqlInputs", "Generated"]


def test_missing_modules_counts_roots_and_glob_prefixes() -> None:
    """`missing_modules` reports a helper module that no library lists, because Lake would not find it; roots,
    exact globs and `X.*` / `X.+` globs count as listed."""
    lakefile = ('[[lean_lib]]\nname = "A"\nroots = ["Proofs"]\n\n'
                '[[lean_lib]]\nname = "B"\nglobs = ["Helpers.+", "Exact"]\n')
    assert missing_modules(lakefile, ["Proofs", "Helpers", "Helpers.Facts", "Exact", "AtuinFacts"]) == ["AtuinFacts"]


def test_contract_library_must_read_the_given_approved_folder(tmp_path: Path) -> None:
    """`reads_contract_from` accepts a lakefile whose library reads both contract modules from the approved
    folder, and refuses one that reads another folder, so `prepare` cannot export a proof of another contract."""
    (tmp_path / "approved").mkdir()
    (tmp_path / "other").mkdir()
    project = tmp_path / "project"
    project.mkdir()
    text = project_lakefile("proofs", "../approved", ["Requirements", "Interpretation"], ["Proofs"])
    assert reads_contract_from(text, project, tmp_path / "approved")
    assert not reads_contract_from(text, project, tmp_path / "other")


def test_settings_that_turn_off_kernel_checking_are_found() -> None:
    """`check_disabling_settings` finds `debug.skipKernelTC` in package and library `leanOptions` and in
    `moreLeanArgs`, because the audit cannot see an option and the proof would build green locally."""
    lakefile = ('[leanOptions]\n"debug.skipKernelTC" = true\n\n'
                '[[lean_lib]]\nname = "Candidate"\nmoreLeanArgs = ["-Ddebug.skipKernelTC=true"]\n')
    assert check_disabling_settings(lakefile) == ["package: leanOptions.debug.skipKernelTC",
                                                  "lean_lib Candidate: moreLeanArgs -Ddebug.skipKernelTC=true"]
    assert check_disabling_settings(project_lakefile("proofs", "../approved", ["Requirements"], ["Proofs"])) == []
