"""Publish query-source observations as corpus v53 (ADR 0019, D5 and D3).

The corpus joins derived sources, ordinary CTEs and stored views. Use the existing native
recorder, shard bindings and replay checks. The separate judge claim lists only cases
measured to agree with the model.
"""

from pathlib import Path

from conformance import authored_common_tables, authored_evidence, authored_query_sources, authored_views
from conformance.authored_query_source_set import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_query_source_set.py"),
    more_definitions=tuple(Path(module.__file__) for module in
                           (authored_query_sources, authored_common_tables, authored_views)),
    source_name="authored-query-sources", part="query-sources", corpus_version=53,
    evidence_kind="query-source-coverage")
"""Query-source coverage and explicit uncertainty/failure boundaries, after counters v52."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay the native query-source observations."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record query sources as a new native corpus directory.")
