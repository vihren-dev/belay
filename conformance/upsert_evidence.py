"""Publish the authored coverage cases of UPSERT as a new corpus (ADR 0012, amendment 4,
slice 5c).

`python -m conformance.upsert_evidence --output DIRECTORY` records the cases of
`conformance.authored_upserts` natively as version 5 records with outputs and writes
them as corpus version 19 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_upserts import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_upserts.py"),
    source_name="authored-upserts", part="upserts", corpus_version=19, evidence_kind="upsert-coverage")
"""The coverage corpus of UPSERT: version 19, after the coverage corpus of rowid
aliases."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of UPSERT."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of UPSERT natively and write them "
                                   "as a new corpus directory.")
