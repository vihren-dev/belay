"""Publish the authored coverage cases of single-table queries as a new corpus (ADR 0012).

`python -m conformance.query_evidence --output DIRECTORY` records the cases of
`conformance.authored_queries` natively as version 5 records with outputs, replays them,
writes them as corpus version 7 with ordinary shard bindings, reads them back and
replays them again. It never replaces an existing directory. Claiming the corpus
for the judge is a separate, owner-approved change (ADR 0011).
"""

import argparse
import hashlib
import json
from pathlib import Path

from conformance.authored_queries import records
from conformance.case_format import Json
from conformance.corpus import load, native_replay
from conformance.corpus_shards import write

SOURCE_NAME = "authored-queries"
"""The authored query definitions, as the shard manifest names them."""
PART_NAME = "queries"
"""The part of each case: a rule of single-table queries."""
CORPUS_VERSION = 7
"""The corpus version after the frozen corpora 1 to 6."""
NATIVE_VERSION = 5
"""Each record has measured limits, error phases and statement outputs."""
EVIDENCE_KIND = "query-coverage"
"""Distinguishes this evidence from the other corpora."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new corpus directory."""
    if directory.exists() or directory.is_symlink():
        raise ValueError(f"Query evidence output already exists: {directory}; choose a new directory")
    acquired = records()
    native_replay(acquired)
    source = Path(__file__).with_name("authored_queries.py")
    manifest = write(directory, [(SOURCE_NAME, PART_NAME, acquired)], corpus_version=CORPUS_VERSION,
                     native_version=NATIVE_VERSION, metadata={"evidenceKind": EVIDENCE_KIND,
                     "definitionsSha256": hashlib.sha256(source.read_bytes()).hexdigest()})
    loaded_manifest, loaded = load(directory)
    if loaded_manifest != manifest or loaded != acquired:
        raise ValueError(f"Query evidence differs after storage: {directory}; inspect the corpus bindings")
    native_replay(loaded)
    return manifest


def main() -> None:
    """Create the corpus directory and print its acquisition receipt."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="New directory for the corpus")
    manifest = publish(parser.parse_args().output)
    print(json.dumps({"recordedCases": manifest["recordedCases"], "casesSha256": manifest["casesSha256"],
                      "nativeReplayPassed": True}))


if __name__ == "__main__":
    main()
