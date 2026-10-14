"""Publish the boundary cases of the admission obligations as a new corpus.

`python -m conformance.obligation_evidence --output DIRECTORY` records the cases of
`conformance.authored_obligations` natively as version 5 records with outputs and writes
them as corpus version 10 through `conformance.authored_evidence`. A later judge change
claims the corpus, with every case `MODEL_UNSUPPORTED`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_obligations import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_obligations.py"),
    source_name="authored-obligations", part="obligations", corpus_version=10, evidence_kind="obligation-boundaries")
"""The obligation boundary corpus: version 10, after the write coverage corpus."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new obligation boundary corpus."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the obligation boundary cases natively and write them as a new corpus directory.")
