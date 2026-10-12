"""Decode the frozen corpora that the judge lock protects, without validating them again.

`conformance.corpus.validated_load` checks a corpus completely: digests, counts,
formats, snapshots, profiles, and acquisition and fidelity evidence. The corpora
that `judge/claims.json` claims are part of the judge lock (ADR 0011,
`integrity/judge.nix`): their bytes cannot change without a change to the
code-owned `integrity/judge.lock.json`. `tests/conformance_locked_corpora_test.py`,
in the `corpora` Nix suite, runs the complete validation on each of them; that
suite runs again whenever a corpus or the validator changes.

`conformance.corpus.load` decodes a corpus at a claimed path with `locked_records`.
Any other directory, such as a copy, a capture or a new freeze, gets the complete
validation.
"""

import gzip
import json
from pathlib import Path

from conformance.case_format import Json
from conformance.native_storage import decoded_record

ROOT = Path(__file__).resolve().parents[1]
CLAIMS = ROOT / "judge" / "claims.json"
"""The judge's claims; each claimed corpus path is locked. Without the file, nothing is locked."""


def locked_directories() -> frozenset[Path]:
    """The directories of the claimed corpora, resolved."""
    if not CLAIMS.is_file():
        return frozenset()
    claims = json.loads(CLAIMS.read_text(encoding="utf-8"))
    return frozenset((ROOT / entry["path"]).resolve() for entry in claims["corpora"].values())


def is_locked(directory: Path) -> bool:
    """Whether the directory is a claimed corpus, whose bytes the judge lock protects."""
    return not directory.is_symlink() and directory.resolve() in locked_directories()


def locked_records(directory: Path, manifest: dict[str, Json]) -> list[dict[str, Json]]:
    """Decode the cases of a locked corpus, in manifest order, without validating them again."""
    paths = [shard["path"] for shard in manifest["shards"]] if "shards" in manifest else ["cases.jsonl.gz"]
    return [record for relative in paths for record in locked_file_records(directory, relative)]


def locked_file_records(directory: Path, relative: str) -> list[dict[str, Json]]:
    """Decode the cases of one shard or case file, so that a caller can process a large corpus one
    file at a time."""
    return [decoded_record(json.loads(line)) for line in gzip.decompress((directory / relative).read_bytes()).splitlines()]
