"""Application interfaces, translation and the two simulation theorems (ADR 0017, S8)."""

from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_assertion_examples_test import check_module_chain
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_interfaces_translation_and_simulations_hold_for_applications(runtime_root: Path, tmp_path: Path) -> None:
    """The installed S8 primitives apply to a shop whose calls have different argument lists, one
    call of two statements and two calls with one script. The program of an application is the
    hand-written program, translation replaces each call by its partner, two witnesses of one
    program translate differently, and the full-state and the scoped theorems hold for an application
    that chooses its later call from an earlier result. The scoped agreement fails for a different
    output, a different value and an unrelated final context. Every theorem uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("ApplicationShop", 5), ("ApplicationSimulations", 7)))


def test_restricted_domain_needs_the_domain_condition(runtime_root: Path, tmp_path: Path) -> None:
    """The domain condition of the full-state simulation is needed. A migration that stores the clock
    of its statement commutes with one read at the start context, because the clock is the same at
    statements 0 and 1. The read leaves the start context, so no simulation exists over it, and the
    application with two reads does not commute with the migration. Every theorem uses only logical
    axioms."""
    check_module_chain(runtime_root, tmp_path, (("ApplicationRestrictedDomain", 4),))


def test_application_branches_keep_choices_errors_stops_and_snapshots(runtime_root: Path, tmp_path: Path) -> None:
    """The branches of an application are the branches of its program. A raw choice between results
    leads to the default call, and each concrete alternative leads to another call. A modeled error is
    an output followed by the next call. A stop ends the application before the next call. A relation
    that names the transaction snapshot tells apart two programs with equal outputs, and a relation
    that ignores it does not. Every theorem uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("ApplicationBranchKinds", 7),))


def test_weak_query_translation_needs_frame_facts_to_become_a_simulation(runtime_root: Path,
                                                                        tmp_path: Path) -> None:
    """A constant query translates weakly across a migration that stores the clock of its statement, and
    still no full-state simulation exists under a clock that changes with the index, because the read
    moves the statement index (fixture ApplicationWeakBridges). When the clock
    gives one date at every index, the read meets the frame facts of the installed query bridge, the
    bridge gives a simulation, and the application with two reads commutes with the migration at every
    admitted context (fixture ApplicationConstantClock). Every theorem uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (
        ("ApplicationRestrictedDomain", 4), ("ApplicationWeakBridges", 2), ("ApplicationConstantClock", 4)))


def test_interface_mistakes_are_diagnosed_where_they_are_written(runtime_root: Path, tmp_path: Path) -> None:
    """Lean rejects each mistake of an interface, pairing or application at its own line: a call
    outside the interface, an argument of the wrong type, a missing entry, an entry with another
    argument type, and a pairing over another signature. The type of a signature is what makes a
    partner exist with the same argument type, so no separate pairing check runs."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ApplicationInterfaceErrors.lean", tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode != 0, result.diagnostic()
    errors = re.findall(r"ApplicationInterfaceErrors\.lean:(\d+):\d+: error[^:]*: (.*)", result.stdout)
    assert [line for line, _ in errors] == ["31", "34", "38", "43", "55"], result.diagnostic()
    text = {int(line): message for line, message in errors}
    assert "Unknown constant `ApplicationInterfaceErrors.Call.remove`" in text[31]
    assert "Application type mismatch" in text[34] and "expected to have type" in result.stdout
    assert "Missing cases" in text[38] and "Call.find" in result.stdout
    assert "Type mismatch" in text[43]
    assert "Application type mismatch" in text[55] and "Interface otherSignature" in result.stdout
