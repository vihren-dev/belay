"""Publish the authored coverage cases of USING and NATURAL joins as a new corpus (ADR 0012, amendment 2, slice 4b).

`python -m conformance.using_evidence --output DIRECTORY` records the cases of
`conformance.authored_using` natively as version 5 records with outputs and writes
them as corpus version 14 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_using import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_using.py"),
    source_name="authored-using", part="using", corpus_version=14, evidence_kind="using-coverage")
"""The USING and NATURAL coverage corpus: version 14, after the join coverage corpus."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new USING and NATURAL coverage corpus."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored USING and NATURAL cases natively and write them "
                                   "as a new corpus directory.")
