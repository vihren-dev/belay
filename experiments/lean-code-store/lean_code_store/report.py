"""The tables of the prototype findings record, from one run's facts, store and query result.

It prints the decisions of the folding rules with examples, the reported constants by cause,
the summed counts of the run, the candidates of the single-use query by kind, and a fixed
sample of candidates with their stored text, for a person to read against the source.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re

from lean_code_store.facts import module_facts
from lean_code_store.folding import decide_module
from lean_code_store.inputs import select_files
from lean_code_store.run import package_argument

EXAMPLES = 3
"""Examples printed for each rule or cause."""


def name_shape(name: str) -> str:
    """The final name component with digits replaced, and a mark for a private root name."""
    final = re.sub(r"\d+", "N", name.split(".")[-1])
    return final + (" (private, no prefix)" if re.match(r"^_private\.[^ ]*?\.0\.[^.]+$", name) else "")


def decisions_table(facts_dir: Path, sources: dict[str, Path]) -> dict[str, object]:
    """The count and examples of each rule, and of each reported cause and name shape."""
    rules: defaultdict[str, list[str]] = defaultdict(list)
    reported: defaultdict[str, list[str]] = defaultdict(list)
    for path in sorted(facts_dir.glob("*.json")):
        facts = module_facts(json.loads(path.read_text()), path.name)
        for name, decision in sorted(decide_module(facts, sources[facts.module].read_text()).items()):
            rules[f"{decision.status} by {decision.rule}"].append(name)
            if decision.status == "reported":
                reported[f"{decision.rule}: {name_shape(name)}"].append(name)
    return {"rules": {k: [len(v), v[:EXAMPLES]] for k, v in sorted(rules.items())},
            "reported": {k: [len(v), v[:EXAMPLES]] for k, v in sorted(reported.items(), key=lambda i: -len(i[1]))}}


def summed_counts(store: Path, snapshot: str) -> dict[str, int]:
    """The counts of all file versions of one snapshot, summed."""
    total: Counter[str] = Counter()
    for line in (store / "snapshots" / snapshot / "snapshot_files.jsonl").read_text().splitlines():
        key = json.loads(line)["file_key"]
        total.update(json.loads((store / "versions" / key / "counts.json").read_text())["counts"])
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
    rows = [json.loads(line) for line in candidates.read_text().splitlines()]
    kinds = Counter(f"{row['target_kind']}, used_in_a_type={row['used_in_a_type']}" for row in rows)
    chosen = sorted(rows, key=lambda row: hashlib.sha256(row["target_name"].encode()).hexdigest())[:sample]
    return {"count": len(rows), "by_kind": dict(kinds.most_common()),
            "sample": [{**row, "text": texts[(row["target_module"], row["target_name"])][:400]}
                       for row in chosen]}


def main() -> int:
    """Print the tables as JSON."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=package_argument, action="append", required=True)
    parser.add_argument("--facts", type=Path, required=True, help="The facts directory of the first run")
    parser.add_argument("--store", type=Path, required=True)
    parser.add_argument("--snapshot", required=True)
    parser.add_argument("--candidates", type=Path, required=True)
    parser.add_argument("--sample", type=int, default=20)
    arguments = parser.parse_args()
    sources = {file.module: file.source for file in select_files(arguments.package)}
    texts = entity_texts(arguments.store, arguments.snapshot)
    print(json.dumps({"decisions": decisions_table(arguments.facts, sources),
                      "counts": summed_counts(arguments.store, arguments.snapshot),
                      "candidates": candidates_table(arguments.candidates, texts, arguments.sample)},
                     indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
