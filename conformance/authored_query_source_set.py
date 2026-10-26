"""The authored cases of corpus v53: derived sources, ordinary CTEs and stored views (ADR 0019, D5).

The three case modules stay separate for their focused kernel tests. This module joins them
in the order of the task so that one corpus holds all native evidence of queries as sources.
"""

from conformance import authored_common_tables, authored_query_sources, authored_views
from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json


def definitions() -> list[QueryCase]:
    """Derived-source, common-table and view cases, with unique names."""
    cases = [*authored_query_sources.definitions(), *authored_common_tables.definitions(),
             *authored_views.definitions()]
    names = [case.name for case in cases]
    if len(names) != len(set(names)):
        raise ValueError("duplicate query-source case names; rename one case")
    return cases


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record the joined cases with the existing native output recorder."""
    return query_records(definitions() if cases is None else cases, part="query-sources")
