"""Publish the authored coverage cases of triggers as a new corpus (ADR 0018, slice 5).

`python -m conformance.trigger_evidence --output DIRECTORY` records the cases of
`conformance.authored_triggers` natively as version 5 records with outputs and writes them as
corpus version 46 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_triggers import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_triggers.py"),
    source_name="authored-triggers", part="triggers", corpus_version=46,
    evidence_kind="trigger-coverage")
"""The coverage corpus of triggers: version 46, after the corpus of foreign keys."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of triggers."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of triggers natively and write them as a new "
                                   "corpus directory.")
