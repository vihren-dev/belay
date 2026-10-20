"""Publish the authored coverage cases of subqueries as a new corpus (ADR 0018, slice 1).

`python -m conformance.subquery_evidence --output DIRECTORY` records the cases of
`conformance.authored_subqueries` natively as version 5 records with outputs and writes them as
corpus version 42 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_subqueries import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_subqueries.py"),
    source_name="authored-subqueries", part="subqueries", corpus_version=42, evidence_kind="subquery-coverage")
"""The coverage corpus of subqueries: version 42, after the corpus of printf."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of subqueries."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of subqueries natively and write them as a new corpus "
                                   "directory.")
