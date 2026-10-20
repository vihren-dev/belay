"""Publish the authored coverage cases of the JSON build and edit functions as a new corpus (ADR 0015, slice 3).

`python -m conformance.json_edit_evidence --output DIRECTORY` records the cases of
`conformance.authored_json_edits` natively as version 5 records with outputs and writes them
as corpus version 38 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_json_edits import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_json_edits.py"),
    source_name="authored-json-edits", part="json-edits", corpus_version=38, evidence_kind="json-edit-coverage")
"""The coverage corpus of the JSON build and edit functions: version 38, after the corpus of the
exact numeric functions."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of the JSON build and edit functions."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of the JSON build and edit functions natively and "
                                   "write them as a new corpus directory.")
