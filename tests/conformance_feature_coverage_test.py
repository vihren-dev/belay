"""The authored coverage cases of the SQL functions, subqueries, parameters, pragmas, compound
SELECT, errors and counters (ADR 0015, 0018, 0019 and 0024): the second of the two coverage test
files (the first is `tests/conformance_query_coverage_test.py`).

The cases of `conformance.authored_text_functions`, `conformance.authored_numeric_functions`,
`conformance.authored_json_edits`, `conformance.authored_jsonb`,
`conformance.authored_aggregates` and `conformance.authored_printf` (ADR 0015, slices 1 to 6),
and `conformance.authored_subqueries`, `conformance.authored_expression_forms` and
`conformance.authored_distinct_having`, `conformance.authored_foreign_keys` and
`conformance.authored_triggers` and `conformance.authored_possible_results` (ADR 0018,
slices 1 to 6; the foreign keys and the triggers under a profile with foreign keys on), and
`conformance.authored_parameters` (ADR 0019, slice 1), which bind values to parameters,
`conformance.authored_pragmas` (ADR 0019, slice 2; its recursive trigger case under a profile
with recursive triggers on) and `conformance.authored_compound` (ADR 0019, slice 3) are
recorded natively as version 5 records with statement outputs, and the cases of
`conformance.authored_after_error` as version 6 records, which run on after an error, and the cases of
`conformance.authored_counters` as version 7 records, which also hold the connection counters (ADR 0024, slice 1),
and the cases of `conformance.authored_foreign_key_atoms` as version 6 records.
They name requirement identifiers of the pinned documentation, and replay through resolution,
the execution semantics and query evaluation. Every case agrees with the model, and the kernel
checks each verdict. The corpus writers that publish each set as a new corpus are checked in
`tests/conformance_corpus_writers_test.py`, a scheduled suite.
"""

from pathlib import Path
from types import ModuleType

import pytest

from conformance import (authored_after_error, authored_aggregates, authored_compound, authored_counters,
                         authored_distinct_having, authored_expression_forms, authored_foreign_key_atoms,
                         authored_foreign_keys, authored_json_edits, authored_jsonb,
                         authored_numeric_functions, authored_parameters, authored_possible_results,
                         authored_pragmas, authored_printf, authored_subqueries, authored_text_functions,
                         authored_triggers)
from tests.coverage_case_support import check_coverage_cases

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]
CASE_SETS = [authored_text_functions, authored_numeric_functions, authored_json_edits, authored_jsonb,
             authored_aggregates, authored_printf, authored_subqueries, authored_expression_forms,
             authored_distinct_having, authored_foreign_keys, authored_triggers, authored_possible_results,
             authored_parameters, authored_compound, authored_pragmas, authored_after_error, authored_counters,
             authored_foreign_key_atoms]
"""The authored case modules: each has `definitions` and `records`."""


@pytest.mark.parametrize("cases", CASE_SETS, ids=lambda module: module.__name__.rsplit(".", 1)[-1])
def test_coverage_cases_agree_with_kernel_proofs(cases: ModuleType, runtime_root: Path, tmp_path: Path) -> None:
    """Every case of the module is a native record with outputs (version 5; version 6 for
    `conformance.authored_after_error` and `conformance.authored_foreign_key_atoms`; version 7 for
    `conformance.authored_counters`), has resolvable
    requirements, has a phase on each error, agrees in the compiled classifier, and has a kernel
    proof of its verdict (`tests.coverage_case_support.check_coverage_cases`)."""
    check_coverage_cases(cases, runtime_root, tmp_path)
