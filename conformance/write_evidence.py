"""Publish the authored coverage cases of writes with output as a new corpus (ADR 0012).

`python -m conformance.write_evidence --output DIRECTORY` records the cases of
`conformance.authored_writes` natively as version 5 records with outputs and writes
them as corpus version 9 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_writes import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_writes.py"), source_name="authored-writes",
    part="writes", corpus_version=9, evidence_kind="write-coverage")
"""The write coverage corpus: version 9, after the number coverage corpus."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new write coverage corpus."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored write cases natively and write them as a new corpus directory.")
