"""Publish derived-query-source observations as corpus v53 (ADR 0019, D5 and D3).

Use the existing native recorder, shard bindings and replay checks. The separate
judge claim lists only cases measured to agree with the model.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_query_sources import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_query_sources.py"),
    source_name="authored-query-sources", part="query-sources", corpus_version=53,
    evidence_kind="query-source-coverage")
"""Derived-source coverage and explicit uncertainty/failure boundaries, after counters v52."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay the native derived-source observations."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record derived SELECT sources as a new native corpus directory.")
