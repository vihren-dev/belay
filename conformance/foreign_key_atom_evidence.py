"""Publish the authored cases of the foreign-key atoms as a new corpus (task "foreign-key facts and
preservation").

`python -m conformance.foreign_key_atom_evidence --output DIRECTORY` records the cases of
`conformance.authored_foreign_key_atoms` natively as version 6 records, which run on after an error,
and writes them as corpus version 54 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_foreign_key_atoms import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_foreign_key_atoms.py"),
    source_name="authored-foreign-key-atoms", part="foreign-key-atoms", corpus_version=54,
    evidence_kind="foreign-key-atom-coverage", native_version=6)
"""The coverage corpus of the foreign-key atoms: version 54, after the corpus of the query sources (version 53)."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of the foreign-key atoms."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of the foreign-key atoms natively and write "
                                   "them as a new corpus directory.")
