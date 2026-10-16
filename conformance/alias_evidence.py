"""Publish the authored coverage cases of rowid aliases as a
new corpus (ADR 0012, amendment 4, slice 5b).

`python -m conformance.alias_evidence --output DIRECTORY` records the cases of
`conformance.authored_aliases` natively as version 5 records with outputs and writes
them as corpus version 18 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_aliases import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_aliases.py"),
    source_name="authored-aliases", part="aliases", corpus_version=18, evidence_kind="alias-coverage")
"""The coverage corpus of rowid aliases: version 18, after
the coverage corpus of unique key values."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of rowid aliases."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of rowid aliases "
                                   "natively and write them "
                                   "as a new corpus directory.")
