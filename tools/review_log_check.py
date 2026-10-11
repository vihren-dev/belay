"""Check that the review log only grows: records are added, and no base record is lost or changed.

`AGENTS.md` forbids editing or deleting review records. CI runs this check in every scope,
so a pull request that changes only documentation and the log can skip the build, and still
cannot change or remove a review record. The log has two parts (`tools/review_records.py`):

- The frozen `reviews/log.jsonl`. Merges of main into a branch reorder lines and can remove a
  line that both sides contain, so the check requires each base line to be present, not a
  position or a count. Branches written before the record files still add lines to it.
- One file per record. Each base file must be present with the same bytes, and each file must
  hold a valid record at the path that its record determines.
"""

import argparse
from collections.abc import Mapping, Sequence
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from tools.review_records import DIRECTORY, FROZEN_LOG, is_record_path, path_problem

LOG = f"{DIRECTORY}/{FROZEN_LOG}"
"""The frozen log path, relative to the repository root."""
REQUIRED_FIELDS = {"review": frozenset({"kind", "id", "commit", "date", "findings", "well_formed"}),
                   "resolution": frozenset({"kind", "finding", "outcome", "date"})}
"""The fields of each record kind, as `tools/review.py` and `tools/review_log.py` write them."""
BASE_VARIABLE = "REVIEW_LOG_BASE"
"""The base commit hash; CI sets it from the event, without passing event data to a shell."""
NO_BASE = "0" * 40
"""Git's hash for a missing commit, which GitHub sends for a new branch."""
GIT_TIMEOUT_SECONDS = 30
"""Reading the reviews directory of one local commit."""


def record_problem(text: str) -> str | None:
    """Why one log line or record file is not a review record, or `None` when it is one."""
    try:
        record = json.loads(text)
    except json.JSONDecodeError:
        return "not JSON"
    if not isinstance(record, dict):
        return "not a JSON object"
    kind = record.get("kind")
    required = REQUIRED_FIELDS.get(kind) if isinstance(kind, str) else None
    if required is None:
        return f"unknown record kind {kind!r}"
    missing = sorted(required - record.keys())
    return f"missing fields {', '.join(missing)}" if missing else None


def problems(base: Sequence[str], head: Sequence[str]) -> list[str]:
    """The violations of the append-only rule from the base frozen log to the head frozen log.

    Each head line must be a record, and each base line must occur in the head log unchanged.
    The rule requires nothing about the order of lines or about repeated lines.
    """
    found = [f"line {number}: {problem}" for number, line in enumerate(head, start=1)
             if (problem := record_problem(line)) is not None]
    present = set(head)
    found += [f"base line {number} is changed or removed" for number, line in enumerate(base, start=1)
              if line not in present]
    return found


def blob_hash(content: bytes) -> str:
    """Git's object id of a file's content, to compare a working-tree file with a base blob."""
    return hashlib.sha1(b"blob %d\0" % len(content) + content).hexdigest()


def file_problems(base: Mapping[str, str], head: Mapping[str, bytes]) -> list[str]:
    """The violations of the append-only rule for record files.

    `base` maps each repository path under `reviews/` to its blob hash in the base commit;
    `head` maps each path under `reviews/` to its working-tree bytes. The frozen log is checked
    by `problems` and is ignored here.
    """
    found: list[str] = []
    for path, content in sorted(head.items()):
        if path == LOG:
            continue
        if not is_record_path(path):
            found.append(f"{path}: not a record file; use ID/review.json or ID/resolution-N-SECOND.json")
            continue
        text = content.decode("utf-8", errors="replace")
        problem = record_problem(text) or path_problem(path.removeprefix(f"{DIRECTORY}/"), json.loads(text))
        if problem is not None:
            found.append(f"{path}: {problem}")
    found += [f"{path}: base record file is changed or removed" for path, blob in sorted(base.items())
              if path != LOG and (path not in head or blob_hash(head[path]) != blob)]
    return found


def git(root: Path, *arguments: str) -> str:
    """The output of one Git command that reads the local repository."""
    return subprocess.run(["git", *arguments], cwd=root, check=True, capture_output=True, text=True,
                          timeout=GIT_TIMEOUT_SECONDS).stdout


def base_files(root: Path, base: str) -> dict[str, str]:
    """The blob hash of each file under `reviews/` in the base commit; a commit without it has none."""
    if re.fullmatch(r"[0-9a-f]{40}", base) is None:
        raise ValueError(f"{BASE_VARIABLE} must be a full commit hash, not {base!r}")
    if base == NO_BASE:
        return {}
    files: dict[str, str] = {}
    for entry in git(root, "ls-tree", "-r", base, "--", f"{DIRECTORY}/").splitlines():
        details, path = entry.split("\t", 1)
        files[path] = details.split()[2]
    return files


def head_files(root: Path) -> dict[str, bytes]:
    """The bytes of each file under `reviews/` in the working tree."""
    directory = root / DIRECTORY
    return {path.relative_to(root).as_posix(): path.read_bytes()
            for path in sorted(directory.rglob("*")) if path.is_file()} if directory.is_dir() else {}


def main(arguments: Sequence[str]) -> int:
    """Check the working-tree log against the base commit in `REVIEW_LOG_BASE`, when it is set."""
    parser = argparse.ArgumentParser(description=main.__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    options = parser.parse_args(arguments)
    base = os.environ.get(BASE_VARIABLE, "")
    base_blobs = base_files(options.root, base) if base else {}
    head = head_files(options.root)
    base_log = git(options.root, "show", f"{base}:{LOG}").splitlines() if LOG in base_blobs else []
    head_log = head[LOG].decode("utf-8").splitlines() if LOG in head else []
    log_problems, record_file_problems = problems(base_log, head_log), file_problems(base_blobs, head)
    for problem in log_problems:
        print(f"review log: {LOG}: {problem}; restore the original line", file=sys.stderr)
    for problem in record_file_problems:
        print(f"review log: {problem}; restore the original record files and add each new record "
              f"with `just review` or `just review-resolve`", file=sys.stderr)
    return 1 if log_problems or record_file_problems else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
