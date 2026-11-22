"""Tests of `lean_code_store.source` and `lean_code_store.mentions`: text cuts and mention users."""

from __future__ import annotations

import json

import pytest

from factories import span
from lean_code_store.mentions import Usage, mention_user, read_usages
from lean_code_store.source import range_text, user_name

pytestmark = [pytest.mark.unit, pytest.mark.timeout(5)]


def test_range_text_and_user_name() -> None:
    """`range_text` cuts at code point columns; `user_name` removes the private prefix."""
    lines = ["def é : Nat := 1", "", "deriving instance BEq, Hashable", "  for A, B", "def x := 2"]
    assert range_text(lines, span(1, 4, 1, 5)) == "é"
    assert range_text(lines, span(3, 0, 4, 10)) == "deriving instance BEq, Hashable\n  for A, B"
    assert user_name("_private.A.B.0.Foo.bar") == "Foo.bar"


def test_read_usages_skips_definitions_and_counts_lines_from_one() -> None:
    """Usages keep their container; a usage without container has `None`."""
    ilean = json.dumps({"references": {
        json.dumps({"c": {"m": "N", "n": "g"}}): {"definition": None, "usages": [[0, 2, 0, 3, "f"], [4, 1, 4, 2]]},
        json.dumps({"f": {"m": "M", "n": "x"}}): {"definition": None, "usages": [[1, 1, 1, 2]]}}})
    assert read_usages(ilean) == [Usage("N", "g", 1, 2, "f"), Usage("N", "g", 5, 1, None)]


def test_mention_user_order() -> None:
    """Container first; else the one smallest containing declaration; else no user."""
    declarations = {"outer": span(1, 0, 9, 0), "outer.go": span(3, 2, 4, 0), "twin1": span(10, 0, 11, 0),
                    "twin2": span(10, 0, 11, 0)}
    resolve = {("M", "outer.match_1"): ("M", "outer"), ("M", "outer"): ("M", "outer")}.get

    def user(line: int, container: str | None) -> tuple[object, str]:
        found = mention_user(Usage("N", "g", line, 3, container), "M", lambda m, n: resolve((m, n)), declarations)
        return found.user, found.source
    assert user(2, "outer.match_1") == (("M", "outer"), "container")
    assert user(3, None) == (("M", "outer.go"), "range")
    assert user(3, "_example") == (("M", "outer.go"), "range")
    assert user(10, None) == (None, "none")
    assert user(20, None) == (None, "none")
