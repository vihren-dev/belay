"""Check lossless review export through the existing reader and statistics functions."""

from collections import Counter
from dataclasses import asdict
import json
from pathlib import Path
import sys

from probe_support import write_json


def measure(root: Path, output: Path) -> None:
    """Round-trip real records without changing them or inventing missing measurements."""
    sys.path.insert(0, str(root))
    from tools.review_log import parse_rules
    from tools.review_records import read_records
    from tools.review_stats import collect

    output.mkdir()
    records = read_records(root / "reviews")
    encoded = "".join(json.dumps(record, sort_keys=True) + "\n" for record in records)
    exported = [json.loads(line) for line in encoded.splitlines()]
    assert exported == records
    rules = parse_rules((root / "docs/review-checklist.md").read_text())
    before, after = collect(records, rules), collect(exported, rules)
    assert before == after
    write_json(output / "statistics.json", {rule: asdict(stats) for rule, stats in after.items()})
    kinds = Counter(str(record["kind"]) for record in records)
    fields = {kind: sorted({field for record in records if record["kind"] == kind for field in record})
              for kind in kinds}
    write_json(output / "summary.json", {"records": len(records), "kinds": dict(kinds),
        "jsonl_bytes": len(encoded.encode()), "fields": fields, "statistics_preserved": True,
        "duration_records": sum("duration" in record for record in records),
        "model_version_records": sum("model" in record or "model_version" in record for record in records)})
