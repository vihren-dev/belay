"""Publish the authored coverage cases of index forms as a
new corpus (ADR 0014, slice 1).

`python -m conformance.index_evidence --output DIRECTORY` records the cases of
`conformance.authored_indexes` natively as version 5 records with outputs and writes
them as corpus version 29 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_indexes import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_indexes.py"),
    source_name="authored-indexes", part="indexes", corpus_version=29, evidence_kind="index-coverage")
"""The coverage corpus of index forms: version 29, after the corpus of date and time
modifiers."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of index forms."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of index forms "
                                   "natively and write them "
                                   "as a new corpus directory.")
