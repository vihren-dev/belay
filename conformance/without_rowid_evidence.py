"""Publish the authored coverage cases of `WITHOUT ROWID` tables as a
new corpus (ADR 0014, slice 2).

`python -m conformance.without_rowid_evidence --output DIRECTORY` records the cases of
`conformance.authored_without_rowid` natively as version 5 records with outputs and writes
them as corpus version 30 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_without_rowid import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_without_rowid.py"),
    source_name="authored-without-rowid", part="without-rowid", corpus_version=30, evidence_kind="without-rowid-coverage")
"""The coverage corpus of `WITHOUT ROWID` tables: version 30, after the corpus of index forms."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of `WITHOUT ROWID` tables."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of `WITHOUT ROWID` tables "
                                   "natively and write them "
                                   "as a new corpus directory.")
