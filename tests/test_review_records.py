"""Review records as one file each, next to the frozen log (`tools/review_records.py`).

The layout exists so that workspaces that record reviews at the same time never change the
same file. These tests check the paths, that no file is ever replaced, and the read order.
"""

from datetime import datetime, timezone
import json
from pathlib import Path, PurePosixPath

import pytest

from tools.review_log import Rule, resolution, review_record
from tools.review_records import (FROZEN_LOG, is_record_path, path_problem, read_records, record_path,
                                  write_record)
from tools.review_stats import collect

WHEN = datetime(2026, 10, 11, 8, 55, 34, tzinfo=timezone.utc)
CHECKLIST = "**R1. One.** Text one.\n*Applies to:* all files.\n\n## Output format\n"
RULES = {"R1": Rule("v1", ("*",))}


def review() -> dict[str, object]:
    """A review of one commit with two findings, as `just review` records it."""
    return review_record(commit="6bb34bbf" * 5, revision="@-", reviewer="codex", caller="claude",
                         files=["A.lean"], checklist=CHECKLIST, exit_code=1, when=WHEN,
                         output="- R1 must A.lean:4 One.\n- R1 should A.lean:9 Two.\n")


@pytest.mark.unit
def test_record_paths() -> None:
    """A review goes to its own directory; a resolution goes next to its review, by finding and second."""
    reviewed = review()
    resolved = resolution([reviewed], "20261011T085534Z-6bb34bbf#2", "fixed", "", WHEN)
    assert record_path(reviewed) == PurePosixPath("20261011T085534Z-6bb34bbf/review.json")
    assert record_path(resolved) == PurePosixPath("20261011T085534Z-6bb34bbf/resolution-2-20261011T085534Z.json")
    for record in (reviewed, resolved):
        assert path_problem(record_path(record).as_posix(), record) is None
        assert is_record_path(f"reviews/{record_path(record)}")
    assert path_problem(record_path(resolved).as_posix(), reviewed) is not None
    assert is_record_path("reviews/log.jsonl") and not is_record_path("reviews/notes.md")
    assert not is_record_path("other/20261011T085534Z-6bb34bbf/review.json")


@pytest.mark.unit
def test_write_creates_one_file_and_never_replaces(tmp_path: Path) -> None:
    """Each record creates one file; the frozen log and other files keep their bytes; a second
    record at the same path is refused and the first file is kept."""
    (tmp_path / FROZEN_LOG).write_text("{}\n")
    reviewed = review()
    first = write_record(reviewed, tmp_path)
    assert json.loads(first.read_text()) == reviewed
    kept = {path: path.read_bytes() for path in tmp_path.rglob("*") if path.is_file()}
    resolved = resolution([reviewed], f"{reviewed['id']}#1", "rejected", "wrong", WHEN)
    second = write_record(resolved, tmp_path)
    assert {path: path.read_bytes() for path in kept} == kept
    assert sorted(path for path in tmp_path.rglob("*") if path.is_file()) == sorted([*kept, second])
    with pytest.raises(ValueError, match="already exists"):
        write_record({**reviewed, "exit": 0}, tmp_path)
    assert json.loads(first.read_text()) == reviewed


@pytest.mark.unit
def test_read_joins_frozen_log_and_files_in_a_fixed_order(tmp_path: Path) -> None:
    """The frozen log comes first in line order, then record files by date, a review before a
    resolution of the same second, then path."""
    reviewed = review()
    frozen = [{"kind": "review", "id": "old", "findings": [], "date": "2026-10-12T00:00:00+00:00"}]
    (tmp_path / FROZEN_LOG).write_text("".join(json.dumps(record) + "\n" for record in frozen))
    later = resolution([reviewed], f"{reviewed['id']}#1", "fixed", "", datetime(2026, 10, 11, 9, tzinfo=timezone.utc))
    earlier = resolution([reviewed], f"{reviewed['id']}#2", "fixed", "", WHEN)
    for record in (later, earlier, reviewed):
        write_record(record, tmp_path)
    (tmp_path / "notes.md").write_text("not a record")
    assert read_records(tmp_path) == [*frozen, reviewed, earlier, later]
    assert read_records(tmp_path / "absent") == []


@pytest.mark.unit
def test_statistics_do_not_depend_on_the_storage(tmp_path: Path) -> None:
    """The same records give the same statistics in the frozen log and as record files."""
    reviewed = review()
    records = [reviewed, resolution([reviewed], f"{reviewed['id']}#1", "rejected", "wrong", WHEN),
               resolution([reviewed], f"{reviewed['id']}#1", "fixed", "", datetime(2026, 10, 12, tzinfo=timezone.utc))]
    reviewed["rules"] = {"R1": "v1"}
    as_log, as_files = tmp_path / "log", tmp_path / "files"
    as_log.mkdir()
    (as_log / FROZEN_LOG).write_text("".join(json.dumps(record) + "\n" for record in records))
    for record in records:
        write_record(record, as_files)
    assert collect(read_records(as_log), RULES) == collect(read_records(as_files), RULES)
    assert collect(read_records(as_files), RULES)["R1"].outcomes["fixed"] == 1
