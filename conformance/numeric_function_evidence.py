"""Publish the authored coverage cases of the exact numeric functions as a new corpus (ADR 0015, slice 2).

`python -m conformance.numeric_function_evidence --output DIRECTORY` records the cases of
`conformance.authored_numeric_functions` natively as version 5 records with outputs and writes
them as corpus version 37 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_numeric_functions import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_numeric_functions.py"),
    source_name="authored-numeric-functions", part="numeric-functions", corpus_version=37, evidence_kind="numeric-function-coverage")
"""The coverage corpus of the exact numeric functions: version 37, after the corpus of the text functions."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of the exact numeric functions."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of the exact numeric functions natively and write them "
                                   "as a new corpus directory.")
