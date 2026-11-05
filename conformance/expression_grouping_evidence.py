"""Publish the authored cases of grouping terms that are expressions as a new corpus (ADR 0030, slice 3).

`python -m conformance.expression_grouping_evidence --output DIRECTORY` records the cases of
`conformance.authored_expression_grouping` natively as version 7 records, which run on after an error and hold the
connection counters, and writes them as corpus version 58 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_expression_grouping import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_expression_grouping.py"),
    source_name="authored-expression-grouping", part="expression-grouping", corpus_version=58,
    evidence_kind="expression-grouping-coverage", native_version=7)
"""The coverage corpus of expression grouping: version 58, after the corpus of the values of a group (version 57)."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of expression grouping."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of expression grouping natively and write "
                                   "them as a new corpus directory.")
