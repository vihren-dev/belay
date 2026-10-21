"""The parse time of the SQL texts of `build/surface-s1/sql.jsonl` (from `texts.py`) with the
Python binding (`belay/sqlite/sql_tree.py`), the baseline of `ParseTime.lean` (ADR 0017, S1).
The garbage collector is off while the texts are parsed, so its pauses are not counted.

Run from the repository root: `python3 experiments/surface-s1/parse_time.py RUNTIME`, with the
conformance runtime root.
"""

import gc
import json
from pathlib import Path
import statistics
import sys
from time import perf_counter

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from belay.sqlite.errors import SqlError  # noqa: E402
from belay.sqlite.sql_tree import SqlParser, parse  # noqa: E402
from conformance.record_parser import runtime_library  # noqa: E402


def main() -> None:
    """Parse each text once with its grammar and print the total, median and largest times."""
    library = runtime_library(Path(sys.argv[1]))
    texts = [json.loads(line) for line in Path("build/surface-s1/sql.jsonl").read_text().splitlines()]
    times, parsed = [], 0
    gc.disable()
    for text in texts:
        started = perf_counter()
        try:
            parse(SqlParser(library, text["grammar"]), text["sql"].encode(), "measured.sql")
            parsed += 1
        except SqlError:
            pass
        times.append(perf_counter() - started)
    gc.enable()
    print(f"texts {len(times)} parsed {parsed} total ms {sum(times) * 1000:.0f} "
          f"median us {statistics.median(times) * 1e6:.0f} max ms {max(times) * 1000:.0f}")


if __name__ == "__main__":
    main()
