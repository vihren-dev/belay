"""Publish the authored coverage cases of the results that SQLite may give as a new corpus (ADR
0018, slice 6).

`python -m conformance.possible_result_evidence --output DIRECTORY` records the cases of
`conformance.authored_possible_results` natively as version 5 records with outputs and writes
them as corpus version 47 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_possible_results import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_possible_results.py"),
    source_name="authored-possible-results", part="possible-results", corpus_version=47,
    evidence_kind="possible-result-coverage")
"""The coverage corpus of the results that SQLite may give: version 47, after the corpus of triggers."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of the results that SQLite may give."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of the results that SQLite may give natively and "
                                   "write them as a new corpus directory.")
