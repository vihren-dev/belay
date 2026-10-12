"""Check that the review log only grows: records are added, and no base record is lost or changed.

`AGENTS.md` forbids editing or deleting review records. CI runs this check in every scope,
so a pull request that changes only documentation and records can skip the build, and still
cannot change or remove a review record. Each record is one file (`tools/review_records.py`):
each base file must be present with the same bytes, and each file must hold a valid record at
the path that its record determines.
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

from tools.review_records import DIRECTORY, is_record_path, path_problem

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


def blob_hash(content: bytes) -> str:
    """Git's object id of a file's content, to compare a working-tree file with a base blob."""
    return hashlib.sha1(b"blob %d\0" % len(content) + content).hexdigest()


def file_problems(base: Mapping[str, str], head: Mapping[str, bytes]) -> list[str]:
    """The violations of the append-only rule for record files.

    `base` maps each repository path under `reviews/` to its blob hash in the base commit;
    `head` maps each path under `reviews/` to its working-tree bytes.
    """
    found: list[str] = []
    for path, content in sorted(head.items()):
        if not is_record_path(path):
            found.append(f"{path}: not a record file; use ID/review.json or ID/resolution-N-SECOND.json")
            continue
        text = content.decode("utf-8", errors="replace")
        problem = record_problem(text) or path_problem(path.removeprefix(f"{DIRECTORY}/"), json.loads(text))
        if problem is not None:
            found.append(f"{path}: {problem}")
    found += [f"{path}: base record file is changed or removed" for path, blob in sorted(base.items())
              if path not in head or blob_hash(head[path]) != blob]
    return found


def git(root: Path, *arguments: str) -> str:
    """The output of one Git command that reads the local repository. CI has Git but no jj, so
    the check reads the base commit with Git."""
    return subprocess.run(["git", *arguments], cwd=root, check=True, capture_output=True, text=True,
                          timeout=GIT_TIMEOUT_SECONDS).stdout


def base_files(root: Path, base: str) -> dict[str, str]:
    """The blob hash of each file under `reviews/` in the base commit; a commit without it has none.
    Comparing blob hashes finds a changed record file without reading each base file."""
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
    """The bytes of each file under `reviews/` in the working tree, which is the change under check.
    Every file is listed, so the check also finds files that are not records."""
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
    found = file_problems(base_blobs, head)
    for problem in found:
        print(f"review log: {problem}; restore the original record files and add each new record "
              f"with `just review` or `just review-resolve`", file=sys.stderr)
    return 1 if found else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
