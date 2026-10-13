"""Publish the authored coverage cases of numbers in queries as a new corpus (ADR 0012).

`python -m conformance.number_evidence --output DIRECTORY` records the cases of
`conformance.authored_numbers` natively as version 5 records with outputs and writes
them as corpus version 8 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_numbers import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_numbers.py"), source_name="authored-numbers",
    part="numbers", corpus_version=8, evidence_kind="number-coverage")
"""The number coverage corpus: version 8, after the query coverage corpus."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new number coverage corpus."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, __doc__)
