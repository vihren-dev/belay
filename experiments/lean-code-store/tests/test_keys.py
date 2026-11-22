"""Tests of `lean_code_store.keys`: the key of a file version and its propagation to importers."""

from __future__ import annotations

import pytest

from lean_code_store.keys import KeyInput, dependency_order, file_key, snapshot_keys

pytestmark = [pytest.mark.unit, pytest.mark.timeout(5)]


def _input(module: str, text: str = "a", imports: tuple[str, ...] = ()) -> KeyInput:
    """A key input with one build product."""
    return KeyInput(module, text * 64, (("M.olean", "b" * 64),), imports)


def test_key_changes_with_each_input() -> None:
    """Each line of the key input changes the key; the order of products and imports does not."""
    base = file_key("x1", "lean", _input("M", imports=("B", "A")), {})
    assert base == file_key("x1", "lean", _input("M", imports=("A", "B")), {})
    assert base != file_key("x2", "lean", _input("M", imports=("A", "B")), {})
    assert base != file_key("x1", "lean2", _input("M", imports=("A", "B")), {})
    assert base != file_key("x1", "lean", _input("N", imports=("A", "B")), {})
    assert base != file_key("x1", "lean", _input("M", "c", ("A", "B")), {})
    assert base != file_key("x1", "lean", _input("M", imports=("A", "B")), {"A": "k" * 64})
    assert len(base) == 64 and base == base.lower()


def test_dependency_order_puts_imports_first_and_rejects_cycles() -> None:
    """A selected import precedes its importer; an import outside the selection is ignored."""
    inputs = {"C": _input("C", imports=("B", "Init")), "B": _input("B", imports=("A",)), "A": _input("A")}
    assert dependency_order(inputs) == ["A", "B", "C"]
    with pytest.raises(ValueError, match="Import cycle"):
        dependency_order({"A": _input("A", imports=("B",)), "B": _input("B", imports=("A",))})


def test_an_edit_changes_the_keys_of_the_importers_only() -> None:
    """An edit of B gives new keys to B and C, which imports B, and not to A or D."""
    inputs = {"A": _input("A"), "B": _input("B", imports=("A",)), "C": _input("C", imports=("B",)),
              "D": _input("D", imports=("A",))}
    before = snapshot_keys("x", "lean", inputs)
    after = snapshot_keys("x", "lean", dict(inputs, B=_input("B", "z", ("A",))))
    assert {m for m in inputs if before[m] != after[m]} == {"B", "C"}
