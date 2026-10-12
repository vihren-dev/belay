"""Check that `judge/claims.json` claims every frozen corpus (ADR 0011).

The `corpora` Nix suite and the judge lock see only the claimed directories, so they cannot
find a new frozen corpus that has no claim. This host check reads the repository instead.
"""

import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [pytest.mark.unit, pytest.mark.conformance]


def test_each_frozen_corpus_directory_is_claimed() -> None:
    """`judge/claims.json` claims each `conformance/corpus-v*` directory and the synthetic
    workload corpus, and nothing else."""
    claims = json.loads((ROOT / "judge/claims.json").read_text())
    claimed = {entry["path"] for entry in claims["corpora"].values()}
    frozen = {path.relative_to(ROOT).as_posix() for path in (ROOT / "conformance").glob("corpus-v*")}
    assert frozen | {"conformance/synthetic-workload/corpus"} == claimed
    assert all((ROOT / directory / "manifest.json").is_file() for directory in claimed)
