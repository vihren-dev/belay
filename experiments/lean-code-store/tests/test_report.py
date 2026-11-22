"""Tests of `lean_code_store.report`: the grouping of reported names and the candidate table."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from lean_code_store.report import candidates_table, name_shape

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
    assert isinstance(table["sample"], list) and len(table["sample"]) == 1
