"""A local store of row files in the write order of the specification.

The prototype writes no database: each table of a file version is a JSON-lines file, and the
`files` row is written last, so a file version without it is not complete.
"""

from __future__ import annotations

import json
from pathlib import Path

from lean_code_store.rows import FileRows, Row

TABLES = ("snapshots", "snapshot_files", "files", "entities", "entity_texts", "entity_references")
"""The six tables of the specification."""


def _write_lines(path: Path, rows: list[Row] | list[dict[str, object]]) -> None:
    """Write rows as JSON lines through a temporary name, so that a reader sees whole files."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".partial")
    temporary.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
    temporary.replace(path)


class LocalStore:
    """Row files below one directory: `versions/KEY/TABLE.jsonl` and `snapshots/ID/TABLE.jsonl`."""

    def __init__(self, root: Path) -> None:
        """Use `root` as the directory of the store."""
        self.root = root

    def version(self, file_key: str) -> Path:
        """The directory of one file version."""
        return self.root / "versions" / file_key

    def is_complete(self, file_key: str) -> bool:
        """Whether the file version has its `files` row."""
        return (self.version(file_key) / "files.jsonl").is_file()

    def write_version(self, file_key: str, rows: FileRows, fold: dict[str, list[str] | None]) -> None:
        """Steps 1 to 4: texts, entities, references, then the `files` row.

        `fold` is a local cache, not a table: the declaration that each constant of the module
        folds into. A later run reads it when it extracts a file that imports this one.
        """
        directory = self.version(file_key)
        _write_lines(directory / "entity_texts.jsonl",
                     [{"text_sha256": digest, "text": text} for digest, text in sorted(rows.texts.items())])
        _write_lines(directory / "entities.jsonl", rows.entities)
        _write_lines(directory / "entity_references.jsonl", rows.references)
        (directory / "fold.json").write_text(json.dumps(fold, sort_keys=True))
        (directory / "counts.json").write_text(json.dumps(
            {"counts": dict(rows.counts), "reported": rows.reported, "decisions": rows.decisions},
            sort_keys=True))
        _write_lines(directory / "files.jsonl", [{"file_key": file_key}])

    def fold(self, file_key: str) -> dict[str, list[str] | None]:
        """The fold cache of a complete file version."""
        loaded: dict[str, list[str] | None] = json.loads((self.version(file_key) / "fold.json").read_text())
        return loaded

    def write_snapshot(self, snapshot: Row, files: list[Row]) -> None:
        """Steps 5 and 6: the files of the snapshot, then the `snapshots` row."""
        directory = self.root / "snapshots" / snapshot["snapshot_id"]
        _write_lines(directory / "snapshot_files.jsonl", files)
        _write_lines(directory / "snapshots.jsonl", [snapshot])
