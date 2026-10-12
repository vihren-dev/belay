"""Review records stored as one file each under `reviews/`.

Each `just review` and `just review-resolve` creates one new file, at a path that its record
determines. Two workspaces therefore never change the same file, and their records merge
without conflicts. See `plans/20261011-review-log-per-record-files.task.md`.

The module uses only the standard library: CI runs the log check on the host without Nix.
"""

from collections.abc import Mapping
from datetime import datetime, timezone
import json
from pathlib import Path, PurePosixPath
import re

DIRECTORY = "reviews"
"""The reviews directory, relative to the repository root."""
REVIEW_ID = r"\d{8}T\d{6}Z-[0-9a-f]{8}"
"""A review id: the UTC second of the review and the first 8 hex digits of the commit."""
STAMP_FORMAT = "%Y%m%dT%H%M%SZ"
"""The UTC second in review ids and resolution file names."""
REVIEW_FILE = re.compile(rf"(?P<review>{REVIEW_ID})/review\.json")
"""The file of one review record, relative to the reviews directory."""
RESOLUTION_FILE = re.compile(rf"(?P<review>{REVIEW_ID})/resolution-(?P<number>[1-9]\d*)-\d{{8}}T\d{{6}}Z\.json")
"""The file of one resolution record: the finding's review and number, then the UTC second."""


def record_path(record: Mapping[str, object]) -> PurePosixPath:
    """The path of a record's file, relative to the reviews directory.

    A review goes to `ID/review.json`. A resolution of finding `ID#N` goes next to its review,
    to `ID/resolution-N-SECOND.json`, so that several outcomes of one finding get several files.
    """
    if record.get("kind") == "review":
        return PurePosixPath(str(record["id"]), "review.json")
    if record.get("kind") == "resolution":
        review, _, number = str(record["finding"]).partition("#")
        moment = datetime.fromisoformat(str(record["date"])).astimezone(timezone.utc)
        return PurePosixPath(review, f"resolution-{number}-{moment.strftime(STAMP_FORMAT)}.json")
    raise ValueError(f"unknown record kind {record.get('kind')!r}")


def path_problem(relative: str, record: Mapping[str, object]) -> str | None:
    """Why a record does not belong at `relative` (inside the reviews directory), or `None`.

    The CI check uses this so that a file name always tells which review or finding it holds.
    """
    if (match := REVIEW_FILE.fullmatch(relative)) is not None:
        if record.get("kind") != "review":
            return "a review.json file must hold a review record"
        return None if record.get("id") == match["review"] else f"review id {record.get('id')!r} does not match the path"
    if (match := RESOLUTION_FILE.fullmatch(relative)) is not None:
        if record.get("kind") != "resolution":
            return "a resolution file must hold a resolution record"
        expected = f"{match['review']}#{match['number']}"
        return None if record.get("finding") == expected else f"finding {record.get('finding')!r} does not match the path"
    return "not a record path; use ID/review.json or ID/resolution-N-SECOND.json"


def is_record_path(repository_path: str) -> bool:
    """Whether a repository path is a record file, so CI can skip the build for records alone."""
    prefix = f"{DIRECTORY}/"
    if not repository_path.startswith(prefix):
        return False
    relative = repository_path.removeprefix(prefix)
    return REVIEW_FILE.fullmatch(relative) is not None or RESOLUTION_FILE.fullmatch(relative) is not None


def encode(record: Mapping[str, object]) -> str:
    """The text of a record file: indented, with sorted keys, so reviews of it read well."""
    return json.dumps(record, ensure_ascii=False, sort_keys=True, indent=2) + "\n"


def write_record(record: Mapping[str, object], directory: Path) -> Path:
    """Create the record's file and return its path. An existing file is never replaced:
    records are history, so a second record at the same path is an error."""
    path = directory / record_path(record)
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open("x", encoding="utf-8") as stream:
            stream.write(encode(record))
    except FileExistsError:
        raise ValueError(f"record file {path} already exists; wait one second and run the command again") from None
    return path


def record_files(directory: Path) -> list[Path]:
    """All record files in the reviews directory, in path order. Readers skip other files, so a
    stray file cannot add a record; the CI check reports such files instead."""
    return sorted(path for path in directory.glob("*/*.json")
                  if path.is_file() and is_record_path(f"{DIRECTORY}/{path.relative_to(directory).as_posix()}"))


def read_records(directory: Path) -> list[dict[str, object]]:
    """All records, by date, reviews before resolutions of the same second, then path.

    The order is the same on every file system, so statistics that break date ties by
    position give the same result everywhere. An absent directory has no records.
    """
    stored = [(json.loads(path.read_text(encoding="utf-8")), path.relative_to(directory).as_posix())
              for path in record_files(directory)]
    stored.sort(key=lambda item: (str(item[0].get("date", "")), item[0].get("kind") != "review", item[1]))
    return [record for record, _ in stored]
