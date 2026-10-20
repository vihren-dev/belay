"""Publish the authored coverage cases of STRICT tables as a new corpus (ADR 0014, slice 6).

`python -m conformance.strict_evidence --output DIRECTORY` records the cases of
`conformance.authored_strict` natively as version 5 records with outputs and writes
them as corpus version 34 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_strict import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_strict.py"),
    source_name="authored-strict", part="strict", corpus_version=34, evidence_kind="strict-coverage")
"""The coverage corpus of STRICT tables: version 34, after the corpus of generated columns."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of STRICT tables."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of STRICT tables natively and write them "
                                   "as a new corpus directory.")
