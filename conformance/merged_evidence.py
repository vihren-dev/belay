"""Publish the authored coverage cases of USING and NATURAL with RIGHT and FULL joins as a
new corpus (ADR 0012, amendment 3, slice 4d).

`python -m conformance.merged_evidence --output DIRECTORY` records the cases of
`conformance.authored_merged` natively as version 5 records with outputs and writes
them as corpus version 16 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_merged import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_merged.py"),
    source_name="authored-merged", part="merged", corpus_version=16, evidence_kind="merged-coverage")
"""The coverage corpus of USING and NATURAL with RIGHT and FULL joins: version 16, after
the RIGHT and FULL coverage corpus."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of USING and NATURAL with RIGHT and FULL joins."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of USING and NATURAL with RIGHT and FULL joins "
                                   "natively and write them "
                                   "as a new corpus directory.")
