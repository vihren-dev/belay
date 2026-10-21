"""Publish the authored coverage cases of DISTINCT and HAVING as a new corpus (ADR 0018, slice 3).

`python -m conformance.distinct_having_evidence --output DIRECTORY` records the cases of
`conformance.authored_distinct_having` natively as version 5 records with outputs and writes
them as corpus version 44 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_distinct_having import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_distinct_having.py"),
    source_name="authored-distinct-having", part="distinct-having", corpus_version=44,
    evidence_kind="distinct-having-coverage")
"""The coverage corpus of DISTINCT and HAVING: version 44, after the corpus of the expression forms."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of DISTINCT and HAVING."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of DISTINCT and HAVING natively and write them as a "
                                   "new corpus directory.")
