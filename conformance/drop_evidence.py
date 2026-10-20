"""Publish the authored coverage cases of DROP INDEX and DROP TABLE as a new corpus (ADR 0014, slice 7).

`python -m conformance.drop_evidence --output DIRECTORY` records the cases of
`conformance.authored_drops` natively as version 5 records with outputs and writes
them as corpus version 35 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_drops import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_drops.py"),
    source_name="authored-drops", part="drops", corpus_version=35, evidence_kind="drop-coverage")
"""The coverage corpus of DROP INDEX and DROP TABLE: version 35, after the corpus of STRICT tables."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of DROP INDEX and DROP TABLE."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of DROP INDEX and DROP TABLE natively and write them "
                                   "as a new corpus directory.")
