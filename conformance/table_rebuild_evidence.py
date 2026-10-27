"""Publish the authored cases of the table rebuild as a new corpus (ADR 0019, D4, slice 5).

`python -m conformance.table_rebuild_evidence --output DIRECTORY` records the cases of
`conformance.authored_table_rebuild_set` natively as version 7 records, which run on after an error and
hold the counters of the writer connection, and writes them as corpus version 55 through
`conformance.authored_evidence`. The separate judge claim lists only the cases that the model
measured to agree.
"""

from pathlib import Path

from conformance import (authored_evidence, authored_table_rebuild_set, column_drop_setups, insert_query_setups,
                         rename_setups)
from conformance.authored_table_rebuild_set import MODULES, PART, records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(authored_table_rebuild_set.__file__),
    more_definitions=tuple(Path(module.__file__) for module in
                           (*MODULES, insert_query_setups, rename_setups, column_drop_setups)),
    source_name="authored-table-rebuild", part=PART, corpus_version=55,
    evidence_kind="table-rebuild-coverage", native_version=7)
"""The coverage corpus of the table rebuild: version 55, after the corpus of the foreign-key atoms (version 54)."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of the table rebuild."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of the table rebuild natively and write "
                                   "them as a new corpus directory.")
