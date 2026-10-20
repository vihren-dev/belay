"""Publish the authored coverage cases of the aggregates `group_concat`, `string_agg` and `total` as
a new corpus (ADR 0015, slice 5).

`python -m conformance.aggregate_evidence --output DIRECTORY` records the cases of
`conformance.authored_aggregates` natively as version 5 records with outputs and writes them as
corpus version 40 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_aggregates import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_aggregates.py"),
    source_name="authored-aggregates", part="aggregates", corpus_version=40, evidence_kind="aggregate-coverage")
"""The coverage corpus of the aggregates: version 40, after the corpus of JSONB."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of the aggregates."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of the aggregates natively and write them as a new corpus "
                                   "directory.")
