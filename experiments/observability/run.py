"""Run explicit observability probes; this does not install production collectors."""

import argparse
import importlib.metadata
from pathlib import Path
import sys

from probe_support import write_json
from python_probe import measure as python_measure
from review_probe import measure as review_measure
from lean_probe import measure as lean_measure
from cost_probe import measure as cost_measure
from context_probe import measure as context_measure
from repository_probe import measure as repository_measure


def main() -> None:
    """Keep every run separate and publish a small summary only after checks pass."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    write_json(output / "versions.json", {"python": sys.version,
        **{name: importlib.metadata.version(name) for name in ("pytest", "pytest-cov", "coverage")}})
    python_measure(output / "python")
    review_measure(args.root.resolve(), output / "reviews")
    lean_measure(args.root.resolve(), output / "lean")
    cost_measure(args.root.resolve(), output / "costs")
    context_measure(args.root.resolve(), output / "context")
    repository_measure(args.root.resolve(), output / "repository")
    print(f"Observability probes passed; evidence: {output}")


if __name__ == "__main__":
    main()
