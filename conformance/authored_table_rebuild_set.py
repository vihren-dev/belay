"""The authored cases of corpus v55: INSERT from a query, renames, DROP COLUMN and the table rebuild
(ADR 0019, D4, slice 5).

The four case modules stay separate for their focused kernel tests. This module joins them in the
order of the task, so that one corpus holds the native evidence of the table rebuild. Every record is a
version 7 record: the migration runs on after an error and the record holds the counters of the writer.
"""

from typing import Protocol

from conformance import authored_column_drops, authored_insert_queries, authored_rebuilds, authored_renames
from conformance.authored_queries import QueryCase
from conformance.case_format import Json


class CaseModule(Protocol):
    """What the corpus needs of a case module: its cases and the native records of a chosen list of them."""

    __file__: str
    """The path of the module source, whose bytes go into the digest of the corpus manifest."""

    def definitions(self) -> list[QueryCase]:
        """All cases of the module."""

    def records(self, cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
        """The native records of the given cases, or of all cases."""


MODULES: tuple[CaseModule, ...] = (authored_insert_queries, authored_renames, authored_column_drops, authored_rebuilds)
"""The case modules of the task, in the order of its parts."""

NOT_FROZEN = frozenset({"insert-query-index-order", "insert-query-index-order-keeps-other-rows"})
"""The cases that native SQLite runs with the source read by its index. The model agrees with them only
through its second execution of the statement (`runPassAllFrom`), but the prediction that the judge
compares is one answer, the model's own execution. The verdict of these cases is DISAGREE, which a claimed
corpus forbids, so the corpus leaves them out. They stay in `conformance.authored_insert_queries` with
their kernel proofs."""

PART = "table-rebuild"
"""The part of every record of the joined corpus; a corpus shard has one part."""


def module_cases(module: CaseModule) -> list[QueryCase]:
    """The cases of one module that the corpus holds: all except those of `NOT_FROZEN`."""
    return [case for case in module.definitions() if case.name not in NOT_FROZEN]


def definitions() -> list[QueryCase]:
    """The cases of the corpus, in module order, with unique names."""
    cases = [case for module in MODULES for case in module_cases(module)]
    names = [case.name for case in cases]
    if len(names) != len(set(names)):
        raise ValueError("duplicate table-rebuild case names; rename one case")
    every_name = {case.name for module in MODULES for case in module.definitions()}
    if not NOT_FROZEN <= every_name:
        raise ValueError(f"NOT_FROZEN names no case: {sorted(NOT_FROZEN - every_name)}; remove or correct "
                         "these names in conformance.authored_table_rebuild_set.NOT_FROZEN")
    return cases


def records() -> list[dict[str, Json]]:
    """Record the cases of each module natively with the recorder of that module, in module order, all
    with the part `PART`."""
    definitions()
    return [{**record, "part": PART} for module in MODULES for record in module.records(module_cases(module))]
