"""Test of `lean_code_store.clickhouse`: the DDL and the single-use query of the specification.

A small store with one snapshot has one declaration with exactly one user, one declaration that
a use outside all declarations also uses, and one declaration without users.
"""

from __future__ import annotations

import json
from pathlib import Path
import shutil

import pytest

from lean_code_store.clickhouse import load_and_query
from lean_code_store.rows import FileRows
from lean_code_store.store import LocalStore

pytestmark = [pytest.mark.requires_clickhouse, pytest.mark.timeout(120)]

SNAPSHOT = "00000000-0000-4000-8000-000000000001"
KEY = "a" * 64


def _reference(user: str, target: str, kind: str) -> dict[str, str]:
    """A relationship row of module `M`."""
    return {"file_key": KEY, "user_module": "M", "user_name": user, "target_module": "M",
            "target_name": target, "kind": kind}


def test_query_returns_the_declaration_with_one_user_only(tmp_path: Path) -> None:
    """`a` has one user; `b` also has a use outside all declarations; `c` has two users; `d` none."""
    clickhouse = shutil.which("clickhouse-local")
    if clickhouse is None:
        pytest.skip("clickhouse-local is not installed")
    store = LocalStore(tmp_path / "store")
    rows = FileRows(
        entities=[{"file_key": KEY, "name": name, "kind": "theorem", "text_sha256": "b" * 64}
                  for name in ("a", "b", "c", "d")],
        texts={"b" * 64: "theorem x : True := trivial"},
        references=[_reference("b", "a", "body"), _reference("c", "b", "type"),
                    _reference("", "b", "mention"), _reference("a", "c", "body"),
                    _reference("b", "c", "body")])
    store.write_version(KEY, rows, {})
    store.write_snapshot({"snapshot_id": SNAPSHOT, "project": "test", "created_at": "2026-11-22 00:00:00.000000"},
                         [{"snapshot_id": SNAPSHOT, "source_path": "M.lean", "module_name": "M", "file_key": KEY}])
    output = tmp_path / "candidates.jsonl"
    summary = load_and_query(Path(clickhouse), store.root, SNAPSHOT, output)
    candidates = [json.loads(line) for line in output.read_text().splitlines()]
    assert [(row["target_name"], row["only_user"], row["used_in_a_type"]) for row in candidates] == \
        [("a", ["M", "b"], 0)]
    assert summary["rows_after_final"] == {"snapshots": 1, "snapshot_files": 1, "files": 1, "entities": 4,
                                           "entity_texts": 1, "entity_references": 5}
