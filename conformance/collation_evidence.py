"""Publish the authored coverage cases of collations as a new corpus (ADR 0014, slice 3).

`python -m conformance.collation_evidence --output DIRECTORY` records the cases of
`conformance.authored_collations` natively as version 5 records with outputs and writes
them as corpus version 31 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_collations import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_collations.py"),
    source_name="authored-collations", part="collations", corpus_version=31, evidence_kind="collation-coverage")
"""The coverage corpus of collations: version 31, after the corpus of `WITHOUT ROWID` tables."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of collations."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of collations natively and write them "
                                   "as a new corpus directory.")
