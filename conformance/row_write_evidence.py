"""Publish the authored coverage cases of row-dependent writes as a new corpus (ADR 0012).

`python -m conformance.row_write_evidence --output DIRECTORY` records the cases of
`conformance.authored_row_writes` natively as version 5 records with outputs and writes
them as corpus version 11 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_row_writes import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_row_writes.py"),
    source_name="authored-row-writes", part="row-writes", corpus_version=11, evidence_kind="row-write-coverage")
"""The row-dependent write coverage corpus: version 11, after the obligation boundary corpus."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new row-dependent write coverage corpus."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored row-dependent write cases natively and write them "
                                   "as a new corpus directory.")
