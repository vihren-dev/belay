"""The equality of candidate B, the translation in C (ADR 0017, S1, prototype 2), with the
Python translation over the texts of `build/surface-s1/texts.jsonl` (from `texts.py`).

The script loads candidate B's library (`candidate-b/`, built as `README.md` says), translates
each text with its grammar, and compares the result with the Python translation's result: the
statements with the value, range and located parts of each node, or the refusal. JSON values
compare with sorted keys, so `true` and `1` differ. The first differences go to
`build/surface-s1/differences-b.jsonl`.

Run from the repository root: `python3 experiments/surface-s1/translate_b.py LIBRARY`.
"""

import json
from pathlib import Path
import sys
from time import perf_counter

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tests.surface_support import candidate_b, candidate_b_result  # noqa: E402

WRITTEN_DIFFERENCES = 50
"""The number of differences written to the file: enough to see their kinds, and a small file."""


def main() -> None:
    """Compare each text and print the counts."""
    library = candidate_b(Path(sys.argv[1]))
    texts = equal = 0
    seconds = 0.0
    with open("build/surface-s1/texts.jsonl") as lines, open("build/surface-s1/differences-b.jsonl", "w") as output:
        for line in lines:
            record = json.loads(line)
            if "python" not in record:
                continue
            started = perf_counter()
            result = candidate_b_result(library, record["grammar"], record["sql"])
            seconds += perf_counter() - started
            texts += 1
            if json.dumps(result, sort_keys=True) == json.dumps(record["python"], sort_keys=True):
                equal += 1
            elif texts - equal <= WRITTEN_DIFFERENCES:
                output.write(json.dumps({"case": record["case"], "role": record["role"], "c": result,
                                         "python": record["python"]}) + "\n")
    print(f"texts {texts} equal {equal} parse, translation and decoding s {seconds:.2f}")


if __name__ == "__main__":
    main()
