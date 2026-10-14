"""Count the corpus cases that each model restriction keeps out of the model's scope.

`python -m conformance.restriction_costs --predictions DIRECTORY` reads the subject's
predictions of the claimed corpora, one `CORPUS.jsonl` file per corpus, as
`nix-build integrity/judge.nix -A predictions` writes them. It counts the cases out
of scope by their cause:

- `restrictions`: the id of a model restriction of name resolution (the registry in
  `Resolution/Restrictions.lean`);
- `frontend`: syntax that the frontend refuses before resolution, by the first clause
  of its message;
- `undeclared`: predicted cases that the subject declares out of scope without a
  refusal, for example cases with bound parameters.

The counts rank which restriction to lift next. They read only the subject's own
predictions, so the locked judge does not change.
"""

import argparse
from collections import Counter
import json
from pathlib import Path

from conformance.case_format import Json


def cause(prediction: dict[str, Json]) -> tuple[str, str] | None:
    """The kind and the name of the cause that keeps a case out of scope, or `None` for a
    case in scope."""
    if prediction.get("status") == "unsupported":
        if "restriction" in prediction:
            return "restrictions", str(prediction["restriction"])
        return "frontend", str(prediction.get("reason", "")).split(";", 1)[0]
    if prediction.get("status") == "predicted" and not prediction.get("supported", True):
        return "undeclared", "out of scope without a refusal"
    return None


def costs(directory: Path) -> dict[str, Json]:
    """The number of cases for each cause, over every corpus file, most frequent first,
    and the number of cases in each corpus."""
    counters: dict[str, Counter[str]] = {"restrictions": Counter(), "frontend": Counter(), "undeclared": Counter()}
    cases: dict[str, int] = {}
    for path in sorted(directory.glob("*.jsonl")):
        lines = [line for line in path.read_text().splitlines() if line.strip()]
        cases[path.stem] = len(lines)
        for line in lines:
            found = cause(json.loads(line))
            if found is not None:
                counters[found[0]][found[1]] += 1
    return {"cases": cases, **{kind: dict(counter.most_common()) for kind, counter in counters.items()}}


def main() -> None:
    """Print the counts as JSON."""
    parser = argparse.ArgumentParser(description="Count the corpus cases that each model restriction keeps out of "
                                                 "scope, from the subject's predictions.")
    parser.add_argument("--predictions", type=Path, required=True, help="Directory of CORPUS.jsonl predictions")
    print(json.dumps(costs(parser.parse_args().predictions), indent=1))


if __name__ == "__main__":
    main()
