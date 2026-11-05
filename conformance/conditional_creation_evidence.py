"""Publish the authored cases of CREATE TABLE and CREATE INDEX with IF NOT EXISTS as a new corpus (ADR 0030, slice 1).

`python -m conformance.conditional_creation_evidence --output DIRECTORY` records the cases of
`conformance.authored_conditional_creation` natively as version 7 records, which run on after an error and hold the
connection counters, and writes them as corpus version 56 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_conditional_creation import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_conditional_creation.py"),
    source_name="authored-conditional-creation", part="conditional-creation", corpus_version=56,
    evidence_kind="conditional-creation-coverage", native_version=7)
"""The coverage corpus of conditional creation: version 56, after the corpus of the table rebuild (version 55)."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of conditional creation."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of conditional creation natively and write "
                                   "them as a new corpus directory.")
