"""Publish the authored coverage cases of generated columns as a new corpus (ADR 0014, slice 5).

`python -m conformance.generated_evidence --output DIRECTORY` records the cases of
`conformance.authored_generated` natively as version 5 records with outputs and writes
them as corpus version 33 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_generated import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_generated.py"),
    source_name="authored-generated", part="generated", corpus_version=33, evidence_kind="generated-coverage")
"""The coverage corpus of generated columns: version 33, after the corpus of CHECK constraints."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of generated columns."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of generated columns natively and write them "
                                   "as a new corpus directory.")
