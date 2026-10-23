"""Publish the authored coverage cases of parameters and bound values as a new corpus (ADR 0019,
slice 1).

`python -m conformance.parameter_evidence --output DIRECTORY` records the cases of
`conformance.authored_parameters` natively as version 5 records with outputs and writes them as
corpus version 48 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_parameters import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_parameters.py"),
    source_name="authored-parameters", part="parameters", corpus_version=48,
    evidence_kind="parameter-coverage")
"""The coverage corpus of parameters: version 48, after the corpus of the results that SQLite may give."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of parameters."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of parameters natively and write them as a new "
                                   "corpus directory.")
