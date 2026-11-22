"""Tests of `lean_code_store.report`: the grouping of reported names and the candidate table."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from lean_code_store.report import candidates_table, decisions_table, name_shape, reported_table

pytestmark = [pytest.mark.unit, pytest.mark.timeout(5)]


def test_name_shape_groups_numbered_and_private_root_names() -> None:
    """Numbers become `N`; a private name with no prefix after the module is marked."""
    assert name_shape("_private.A.B.0.match_12") == "match_N (private, no prefix)"
    assert name_shape("_private.A.B.0.f.match_1.eq_2") == "eq_N"


def test_candidates_table_counts_kinds_and_adds_texts(tmp_path: Path) -> None:
    """Each candidate is counted by kind; the sample carries the stored text."""
    rows = [{"target_module": "M", "target_name": n, "target_kind": "theorem", "only_user": ["M", "u"],
             "used_in_a_type": 0} for n in ("a", "b")]
    path = tmp_path / "candidates.jsonl"
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))
    table = candidates_table(path, {("M", "a"): "theorem a", ("M", "b"): "theorem b"}, 1)
    assert table["count"] == 2
    assert table["by_kind"] == {"theorem, used_in_a_type=0": 2}
    first = min(("a", "b"), key=lambda name: hashlib.sha256(name.encode()).hexdigest())
    assert table["sample"] == [{**rows[("a", "b").index(first)], "text": f"theorem {first}"}]


def test_reported_table_reads_the_stored_causes(tmp_path: Path) -> None:
    """A generated constant whose parent is reported is in the table with its own cause."""
    version = tmp_path / "versions" / "k"
    version.mkdir(parents=True)
    version.joinpath("counts.json").write_text(json.dumps({"counts": {}, "reported": [
        ["_private.M.0.match_1", "no rule"],
        ["_private.M.0.match_1.eq_1", "generated, no declaration at the end of its parents"]]}))
    table = reported_table(tmp_path, {"M": "k"})
    assert table == {"no rule: match_N (private, no prefix)": [1, ["_private.M.0.match_1"]],
                     "generated, no declaration at the end of its parents: eq_N":
                         [1, ["_private.M.0.match_1.eq_1"]]}


def test_decisions_table_needs_the_facts_of_every_module(tmp_path: Path) -> None:
    """Facts of an incremental run, which lack modules, are refused."""
    with pytest.raises(ValueError, match="missing for example"):
        decisions_table(tmp_path, {}, {"M"})
