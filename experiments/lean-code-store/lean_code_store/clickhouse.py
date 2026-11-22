"""Load the local row files into `clickhouse-local` and run the single-use query.

The DDL and the query are read from the specification document, so that the prototype runs
the text that the specification gives. No ClickHouse server is used.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from lean_code_store.store import TABLES

SPECIFICATION = Path(__file__).resolve().parents[3] / "docs" / "records" / "spec-lean-code-store.md"
"""The specification whose DDL and query the prototype runs."""

CLICKHOUSE_TIMEOUT_SECONDS = 600
"""Bound of one `clickhouse-local` call; the load of the default selection takes seconds."""


def specification_sql(text: str) -> tuple[str, str]:
    """The DDL (the first SQL block) and the query for declarations with one user."""
    blocks = re.findall(r"```sql\n(.*?)```", text, flags=re.DOTALL)
    queries = [block for block in blocks if block.lstrip().startswith("WITH files AS")]
    if not blocks or len(queries) != 1:
        raise ValueError(f"{SPECIFICATION}: expected the DDL block and one single-use query block")
    return blocks[0], queries[0].strip().rstrip(";")


def gather(store: Path, destination: Path) -> dict[str, int]:
    """Concatenate the rows of each table of all complete file versions and snapshots."""
    counts: dict[str, int] = {}
    complete = [d for d in sorted((store / "versions").iterdir()) if (d / "files.jsonl").is_file()]
    snapshots = [d for d in sorted((store / "snapshots").iterdir()) if (d / "snapshots.jsonl").is_file()]
    for table in TABLES:
        sources = snapshots if table in ("snapshots", "snapshot_files") else complete
        with (destination / f"{table}.jsonl").open("w") as output:
            counts[table] = 0
            for directory in sources:
                text = (directory / f"{table}.jsonl").read_text()
                output.write(text)
                counts[table] += text.count("\n")
    return counts


def load_and_query(clickhouse: Path, store: Path, snapshot: str, output: Path) -> dict[str, object]:
    """Create the tables, insert the rows, count the rows, and write the query result."""
    ddl, query = specification_sql(SPECIFICATION.read_text())
    with tempfile.TemporaryDirectory(dir=store, prefix="clickhouse-") as temporary:
        work = Path(temporary)
        gathered = gather(store, work)
        statements = [ddl]
        statements += [f"INSERT INTO lean_code.{table} FROM INFILE '{work / (table + '.jsonl')}' FORMAT JSONEachRow;"
                       for table in TABLES]
        statements += [f"SELECT '{table}', count() FROM lean_code.{table} FINAL FORMAT TSV;" for table in TABLES]
        statements.append(f"SELECT * FROM ({query}) ORDER BY target_module, target_name "
                          f"INTO OUTFILE '{output}' TRUNCATE FORMAT JSONEachRow;")
        result = subprocess.run(
            [str(clickhouse), "--path", str(work / "data"), f"--param_snapshot={snapshot}",
             "--multiquery", "--query", "\n".join(statements)],
            check=True, text=True, capture_output=True, timeout=CLICKHOUSE_TIMEOUT_SECONDS)
    loaded = {line.split("\t")[0]: int(line.split("\t")[1]) for line in result.stdout.splitlines() if line}
    return {"rows_in_files": gathered, "rows_after_final": loaded,
            "candidates": sum(1 for _ in output.open())}


def main() -> int:
    """Load a local store and run the single-use query for one snapshot."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--store", type=Path, required=True)
    parser.add_argument("--snapshot", required=True)
    parser.add_argument("--output", type=Path, required=True, help="JSON-lines file for the candidates")
    parser.add_argument("--clickhouse", type=Path, default=Path(shutil.which("clickhouse-local") or "clickhouse-local"))
    arguments = parser.parse_args()
    summary = load_and_query(arguments.clickhouse, arguments.store.resolve(), arguments.snapshot,
                             arguments.output.resolve())
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
