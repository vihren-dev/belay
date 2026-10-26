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
