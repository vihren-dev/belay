"""Publish the authored coverage cases of the text and type functions as a new corpus (ADR 0015, slice 1).

`python -m conformance.text_function_evidence --output DIRECTORY` records the cases of
`conformance.authored_text_functions` natively as version 5 records with outputs and writes
them as corpus version 36 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_text_functions import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_text_functions.py"),
    source_name="authored-text-functions", part="text-functions", corpus_version=36, evidence_kind="text-function-coverage")
"""The coverage corpus of the text and type functions and LIKE and GLOB: version 36, after the corpus of DROP."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of the text and type functions."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of the text and type functions natively and write them "
                                   "as a new corpus directory.")
