"""Publish the authored coverage cases of RIGHT and FULL joins as a new corpus (ADR 0012, amendment 3, slice 4c).

`python -m conformance.right_evidence --output DIRECTORY` records the cases of
`conformance.authored_right` natively as version 5 records with outputs and writes
them as corpus version 15 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_right import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_right.py"),
    source_name="authored-right", part="right", corpus_version=15, evidence_kind="right-coverage")
"""The RIGHT and FULL coverage corpus: version 15, after the USING and NATURAL coverage corpus."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new RIGHT and FULL coverage corpus."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored RIGHT and FULL cases natively and write them "
                                   "as a new corpus directory.")
