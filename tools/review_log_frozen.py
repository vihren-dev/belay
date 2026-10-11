"""`just review-log-frozen`: whether `reviews/log.jsonl` has stopped changing on every branch.

New review records are files (`tools/review_records.py`), but branches that started before
that change can still bring new lines to the frozen log. The log can be converted to record
files only when no branch or workspace holds a line that `main` lacks; otherwise the
conversion would lose that branch's records, or the branch would conflict with it. See
`plans/20261011-review-log-per-record-files.task.md`.

The command reads the jj repository and changes nothing. A workspace counts with its last
snapshot; run a jj command in that workspace first to include newer changes.
"""

import argparse
from collections.abc import Sequence
from dataclasses import dataclass
import subprocess
from pathlib import Path
import sys

from tools.review_log import ROOT
from tools.review_records import DIRECTORY, FROZEN_LOG

LOG = f"{DIRECTORY}/{FROZEN_LOG}"
"""The frozen log, relative to the repository root."""
JJ_TIMEOUT_SECONDS = 30
"""One local, read-only jj query."""
HEADS = "(bookmarks() | remote_bookmarks() | working_copies()) ~ ::({main})"
"""Every branch and workspace that `main` does not contain yet."""


@dataclass(frozen=True)
class Head:
    """One unmerged branch or workspace commit, its names, and its frozen-log lines."""

    commit: str
    names: str
    lines: frozenset[str]


def missing_lines(main: frozenset[str], head: Head) -> int:
    """The number of frozen-log lines of `head` that `main` lacks; these block the conversion."""
    return len(head.lines - main)


def describe(main: frozenset[str], head: Head) -> str:
    """One report line: the head's names and how its frozen log compares with `main`'s."""
    missing = missing_lines(main, head)
    state = ("same as main" if head.lines == main else "older than main" if not missing
             else f"{missing} {'line' if missing == 1 else 'lines'} that main lacks")
    return f"{head.commit[:12]} {head.names}: {state}"


def jj(root: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
    """Run one read-only jj query without a working-copy snapshot, so nothing changes."""
    return subprocess.run(["jj", "--ignore-working-copy", *arguments], cwd=root, capture_output=True,
                          text=True, timeout=JJ_TIMEOUT_SECONDS, check=False)


def log_lines(root: Path, revision: str) -> frozenset[str]:
    """The non-empty frozen-log lines of a revision; a revision without the log has none."""
    result = jj(root, "file", "show", "-r", revision, LOG)
    if result.returncode and "No such path" in result.stderr:
        return frozenset()
    if result.returncode:
        raise RuntimeError(f"cannot read {LOG} at {revision}: {result.stderr.strip()}")
    return frozenset(line for line in result.stdout.splitlines() if line.strip())


def heads(root: Path, main: str) -> list[Head]:
    """Every branch and workspace commit that `main` does not contain, with its frozen log."""
    template = 'commit_id ++ "\\t" ++ separate(" ", bookmarks, working_copies) ++ "\\n"'
    result = jj(root, "log", "--no-graph", "-r", HEADS.format(main=main), "-T", template)
    if result.returncode:
        raise RuntimeError(f"cannot list branches and workspaces: {result.stderr.strip()}")
    entries = [line.split("\t", 1) for line in result.stdout.splitlines() if line.strip()]
    return [Head(commit, names, log_lines(root, commit)) for commit, names in entries]


def main(arguments: Sequence[str]) -> int:
    """Report each unmerged branch and workspace; exit 0 when none has a line that main lacks."""
    parser = argparse.ArgumentParser(prog="just review-log-frozen", description=main.__doc__)
    parser.add_argument("--main", default="main", help="the revision to compare with (default: main)")
    parser.add_argument("--root", type=Path, default=ROOT, help="the jj repository (default: this one)")
    options = parser.parse_args(arguments)
    try:
        reference = log_lines(options.root, options.main)
        found = heads(options.root, options.main)
    except (OSError, subprocess.TimeoutExpired, RuntimeError) as error:
        print(f"review-log-frozen: {error}. Run `jj git fetch` and try again.", file=sys.stderr)
        return 2
    for head in found:
        print(describe(reference, head))
    blocking = [head for head in found if missing_lines(reference, head)]
    print(f"{len(found)} unmerged branches and workspaces; {len(blocking)} have frozen-log lines that "
          f"{options.main} lacks." + ("" if blocking else " The frozen log can be converted."))
    return 1 if blocking else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
