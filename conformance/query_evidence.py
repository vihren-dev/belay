"""Publish the authored coverage cases of single-table queries as a new corpus (ADR 0012).

`python -m conformance.query_evidence --output DIRECTORY` records the cases of
`conformance.authored_queries` natively as version 5 records with outputs and writes
them as corpus version 7 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_queries import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_queries.py"), source_name="authored-queries",
    part="queries", corpus_version=7, evidence_kind="query-coverage")
"""The query coverage corpus: version 7, after the frozen corpora 1 to 6."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new query coverage corpus."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, __doc__)
