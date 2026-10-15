"""Publish the authored coverage cases of unique key values as a
new corpus (ADR 0012, amendment 4, slice 5a).

`python -m conformance.key_evidence --output DIRECTORY` records the cases of
`conformance.authored_keys` natively as version 5 records with outputs and writes
them as corpus version 17 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_keys import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_keys.py"),
    source_name="authored-keys", part="keys", corpus_version=17, evidence_kind="key-coverage")
"""The coverage corpus of unique key values: version 17, after
the corpus of USING and NATURAL with RIGHT and FULL joins."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of unique key values."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of unique key values "
                                   "natively and write them "
                                   "as a new corpus directory.")
