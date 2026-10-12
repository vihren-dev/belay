"""Review records as one file each (`tools/review_records.py`).

The layout exists so that workspaces that record reviews at the same time never change the
same file. These tests check the paths, that no file is ever replaced, and the read order.
"""

from datetime import datetime, timezone
import json
from pathlib import Path, PurePosixPath

import pytest

from tools.review_log import resolution, review_record
from tools.review_records import is_record_path, path_problem, read_records, record_path, write_record

WHEN = datetime(2026, 10, 11, 8, 55, 34, tzinfo=timezone.utc)
CHECKLIST = "**R1. One.** Text one.\n*Applies to:* all files.\n\n## Output format\n"


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
    assert not is_record_path("reviews/log.jsonl") and not is_record_path("reviews/notes.md")
    assert not is_record_path("other/20261011T085534Z-6bb34bbf/review.json")


@pytest.mark.unit
def test_write_creates_one_file_and_never_replaces(tmp_path: Path) -> None:
    """Each record creates one file; other files keep their bytes; a second record at the same
    path is refused and the first file is kept."""
    (tmp_path / "notes.md").write_text("kept\n")
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
def test_read_orders_files_by_date(tmp_path: Path) -> None:
    """Record files come by date, a review before a resolution of the same second, then path;
    other files are not records."""
    reviewed = review()
    later = resolution([reviewed], f"{reviewed['id']}#1", "fixed", "", datetime(2026, 10, 11, 9, tzinfo=timezone.utc))
    earlier = resolution([reviewed], f"{reviewed['id']}#2", "fixed", "", WHEN)
    for record in (later, earlier, reviewed):
        write_record(record, tmp_path)
    (tmp_path / "notes.md").write_text("not a record")
    (tmp_path / "log.jsonl").write_text(json.dumps(reviewed) + "\n")
    assert read_records(tmp_path) == [reviewed, earlier, later]
    assert read_records(tmp_path / "absent") == []
