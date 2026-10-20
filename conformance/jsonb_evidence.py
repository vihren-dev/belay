"""Publish the authored coverage cases of JSONB as a new corpus (ADR 0015, slice 4).

`python -m conformance.jsonb_evidence --output DIRECTORY` records the cases of
`conformance.authored_jsonb` natively as version 5 records with outputs and writes them as
corpus version 39 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_jsonb import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_jsonb.py"),
    source_name="authored-jsonb", part="jsonb", corpus_version=39, evidence_kind="jsonb-coverage")
"""The coverage corpus of JSONB: version 39, after the corpus of the JSON build and edit functions."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of JSONB."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of JSONB natively and write them as a new corpus "
                                   "directory.")
