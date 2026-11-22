"""The tables of the prototype findings record, from one snapshot of a store and its query result.

It reads only the stored file versions of the snapshot. It prints the decisions of the
folding rules with examples, the reported constants by cause, the summed counts, the
candidates of the single-use query by kind, and a fixed sample of candidates with their full
stored text, for a person to read against the source.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
from typing import TypedDict


EXAMPLES = 3
"""Examples printed for each rule or cause."""


class Candidate(TypedDict):
    """One row of the single-use query result."""

    target_module: str
    target_name: str
    target_kind: str
    only_user: list[str]
    used_in_a_type: int


def snapshot_keys(store: Path, snapshot: str) -> dict[str, str]:
    """The file key of each module of a snapshot that has its `snapshots` row."""
    if not (store / "snapshots" / snapshot / "snapshots.jsonl").is_file():
        raise ValueError(f"{store}: snapshot {snapshot} has no snapshots row, so it is not complete; "
                         "use a snapshot that a run finished")
    rows: list[SnapshotFile] = [json.loads(line) for line in
                                (store / "snapshots" / snapshot / "snapshot_files.jsonl").read_text().splitlines()]
    return {row["module_name"]: row["file_key"] for row in rows}


def name_shape(name: str) -> str:
    """The final name component with digits replaced, and a mark for a private root name."""
    final = re.sub(r"\d+", "N", name.split(".")[-1])
    return final + (" (private, no prefix)" if re.match(r"^_private\.[^ ]*?\.0\.[^.]+$", name) else "")


class SnapshotFile(TypedDict):
    """One stored `snapshot_files` row."""

    snapshot_id: str
    source_path: str
    module_name: str
    file_key: str


class StoredCounts(TypedDict):
    """The `counts.json` of one file version: counts, reported constants and decisions."""

    counts: dict[str, int]
    reported: list[list[str]]
    """`[name, cause]` pairs."""
    decisions: dict[str, str]


def stored_counts(store: Path, file_key: str) -> StoredCounts:
    """The `counts.json` of one file version; an older version lacks the decisions."""
    loaded: StoredCounts = json.loads((store / "versions" / file_key / "counts.json").read_text())
    if "decisions" not in loaded:
        raise ValueError(f"{store}: file version {file_key} has no decisions; extract the snapshot "
                         "again with the current prototype into a new store")
    return loaded


def decisions_table(store: Path, keys: dict[str, str]) -> dict[str, object]:
    """The count and examples of each decision of the snapshot's file versions."""
    rules: defaultdict[str, list[str]] = defaultdict(list)
    for module in sorted(keys):
        for name, decision in sorted(stored_counts(store, keys[module])["decisions"].items()):
            rules[decision].append(name)
    return {k: [len(v), v[:EXAMPLES]] for k, v in sorted(rules.items())}


def reported_table(store: Path, keys: dict[str, str]) -> dict[str, object]:
    """The reported constants of the stored file versions by cause and name shape.

    It includes the generated constants whose parents end in a reported constant.
    """
    reported: defaultdict[str, list[str]] = defaultdict(list)
    for module in sorted(keys):
        for name, cause in stored_counts(store, keys[module])["reported"]:
            reported[f"{cause}: {name_shape(name)}"].append(name)
    return {k: [len(v), v[:EXAMPLES]] for k, v in sorted(reported.items(), key=lambda i: -len(i[1]))}


def summed_counts(store: Path, keys: dict[str, str]) -> dict[str, int]:
    """The counts of all file versions of one snapshot, summed."""
    total: Counter[str] = Counter()
    for key in keys.values():
        total.update(stored_counts(store, key)["counts"])
    return dict(sorted(total.items()))


def entity_texts(store: Path, snapshot: str) -> dict[tuple[str, str], str]:
    """The stored text of each declaration of a snapshot, by module and name."""
    texts: dict[tuple[str, str], str] = {}
    for line in (store / "snapshots" / snapshot / "snapshot_files.jsonl").read_text().splitlines():
        file = json.loads(line)
        version = store / "versions" / file["file_key"]
        by_hash = {row["text_sha256"]: row["text"] for row in
                   map(json.loads, (version / "entity_texts.jsonl").read_text().splitlines())}
        for row in map(json.loads, (version / "entities.jsonl").read_text().splitlines()):
            texts[(file["module_name"], row["name"])] = by_hash[row["text_sha256"]]
    return texts


def candidates_table(candidates: Path, texts: dict[tuple[str, str], str], sample: int) -> dict[str, object]:
    """The candidates by kind and by `used_in_a_type`, and a sample chosen by name hash."""
    rows: list[Candidate] = [json.loads(line) for line in candidates.read_text().splitlines()]
    kinds = Counter(f"{row['target_kind']}, used_in_a_type={row['used_in_a_type']}" for row in rows)
    chosen = sorted(rows, key=lambda row: hashlib.sha256(row["target_name"].encode()).hexdigest())[:sample]
    return {"count": len(rows), "by_kind": dict(kinds.most_common()),
            "sample": [{**row, "text": texts[(row["target_module"], row["target_name"])]}
                       for row in chosen]}


def main() -> int:
    """Print the tables as JSON."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--store", type=Path, required=True)
    parser.add_argument("--snapshot", required=True)
    parser.add_argument("--candidates", type=Path, required=True)
    parser.add_argument("--sample", type=int, default=20)
    arguments = parser.parse_args()
    texts = entity_texts(arguments.store, arguments.snapshot)
    keys = snapshot_keys(arguments.store, arguments.snapshot)
    print(json.dumps({"decisions": decisions_table(arguments.store, keys),
                      "reported": reported_table(arguments.store, keys),
                      "counts": summed_counts(arguments.store, keys),
                      "candidates": candidates_table(arguments.candidates, texts, arguments.sample)},
                     indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
