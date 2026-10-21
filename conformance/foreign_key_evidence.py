"""Publish the authored coverage cases of enforced foreign keys as a new corpus (ADR 0018, slice 4).

`python -m conformance.foreign_key_evidence --output DIRECTORY` records the cases of
`conformance.authored_foreign_keys` natively as version 5 records with outputs and writes
them as corpus version 45 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_foreign_keys import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_foreign_keys.py"),
    source_name="authored-foreign-keys", part="foreign-keys", corpus_version=45,
    evidence_kind="foreign-key-coverage")
"""The coverage corpus of foreign keys: version 45, after the corpus of DISTINCT and HAVING."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of foreign keys."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of foreign keys natively and write them as a "
                                   "new corpus directory.")
