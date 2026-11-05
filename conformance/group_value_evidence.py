"""Publish the authored cases of the values of a group of an aggregate query as a new corpus (ADR 0030, slice 2).

`python -m conformance.group_value_evidence --output DIRECTORY` records the cases of
`conformance.authored_group_values` natively as version 7 records, which run on after an error and hold the
connection counters, and writes them as corpus version 57 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_group_values import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_group_values.py"),
    source_name="authored-group-values", part="group-values", corpus_version=57,
    evidence_kind="group-values-coverage", native_version=7)
"""The coverage corpus of values of a group: version 57, after the corpus of conditional creation (version 56)."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of values of a group."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of values of a group natively and write "
                                   "them as a new corpus directory.")
