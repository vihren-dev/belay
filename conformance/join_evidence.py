"""Publish the authored coverage cases of joins as a new corpus (ADR 0012, amendment 2, slice 4).

`python -m conformance.join_evidence --output DIRECTORY` records the cases of
`conformance.authored_joins` natively as version 5 records with outputs and writes
them as corpus version 13 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_joins import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_joins.py"),
    source_name="authored-joins", part="joins", corpus_version=13, evidence_kind="join-coverage")
"""The join coverage corpus: version 13, after the DELETE coverage corpus."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new join coverage corpus."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored join cases natively and write them "
                                   "as a new corpus directory.")
