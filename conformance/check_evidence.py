"""Publish the authored coverage cases of CHECK constraints as a new corpus (ADR 0014, slice 4).

`python -m conformance.check_evidence --output DIRECTORY` records the cases of
`conformance.authored_checks` natively as version 5 records with outputs and writes
them as corpus version 32 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_checks import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_checks.py"),
    source_name="authored-checks", part="checks", corpus_version=32, evidence_kind="check-coverage")
"""The coverage corpus of CHECK constraints: version 32, after the corpus of collations."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of CHECK constraints."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of CHECK constraints natively and write them "
                                   "as a new corpus directory.")
