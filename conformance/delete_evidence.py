"""Publish the authored coverage cases of DELETE as a new corpus (ADR 0012, slice 3c).

`python -m conformance.delete_evidence --output DIRECTORY` records the cases of
`conformance.authored_deletes` natively as version 5 records with outputs and writes
them as corpus version 12 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_deletes import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_deletes.py"),
    source_name="authored-deletes", part="deletes", corpus_version=12, evidence_kind="delete-coverage")
"""The DELETE coverage corpus: version 12, after the row-dependent write coverage corpus."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new DELETE coverage corpus."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored DELETE cases natively and write them "
                                   "as a new corpus directory.")
