"""The authored coverage cases of queries, numbers, writes and index forms (ADR 0012, slices 1 to
6g; ADR 0014): the first of the two coverage test files (the second is
`tests/conformance_feature_coverage_test.py`).

The cases of `conformance.authored_queries`, `conformance.authored_numbers`,
`conformance.authored_writes`, `conformance.authored_row_writes`,
`conformance.authored_deletes`, `conformance.authored_joins`,
`conformance.authored_using`, `conformance.authored_right`,
`conformance.authored_merged`, `conformance.authored_keys`,
`conformance.authored_aliases`, `conformance.authored_upserts`,
`conformance.authored_algorithms`, `conformance.authored_fromless`,
`conformance.authored_json`, `conformance.authored_json_functions`,
`conformance.authored_json_each`, `conformance.authored_default_writes`,
`conformance.authored_clock`, `conformance.authored_date_functions` and
`conformance.authored_date_modifiers` (these three under the controlled clock), and
`conformance.authored_indexes`, `conformance.authored_without_rowid`,
`conformance.authored_collations`, `conformance.authored_checks`,
`conformance.authored_generated`, `conformance.authored_strict` and
`conformance.authored_drops` (ADR 0014, slices 1 to 7) are recorded natively as version 5
records with statement outputs. They name requirement identifiers of the pinned documentation,
and replay through resolution, the execution semantics and query evaluation. Every case agrees
with the model, and the kernel checks each verdict, so the query and number semantics and their
proofs run on the same cases. The corpus writers that publish each set as a new corpus are
checked in `tests/conformance_corpus_writers_test.py`, a scheduled suite.
"""

from pathlib import Path
from types import ModuleType

import pytest

from conformance import (authored_algorithms, authored_aliases, authored_checks, authored_clock,
                         authored_collations, authored_date_functions, authored_date_modifiers,
                         authored_default_writes, authored_deletes, authored_drops, authored_fromless,
                         authored_generated, authored_indexes, authored_joins, authored_json,
                         authored_json_each, authored_json_functions, authored_keys, authored_merged,
                         authored_numbers, authored_queries, authored_right, authored_row_writes,
                         authored_strict, authored_upserts, authored_using, authored_without_rowid,
                         authored_writes)
from tests.coverage_case_support import check_coverage_cases

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]
CASE_SETS = [authored_queries, authored_numbers, authored_writes, authored_row_writes, authored_deletes,
             authored_joins, authored_using, authored_right, authored_merged, authored_keys,
             authored_aliases, authored_upserts, authored_algorithms, authored_fromless, authored_json,
             authored_json_functions, authored_json_each, authored_default_writes, authored_clock,
             authored_date_functions, authored_date_modifiers, authored_indexes, authored_without_rowid,
             authored_collations, authored_checks, authored_generated, authored_strict, authored_drops]
"""The authored case modules: each has `definitions` and `records`."""


@pytest.mark.parametrize("cases", CASE_SETS, ids=lambda module: module.__name__.rsplit(".", 1)[-1])
def test_coverage_cases_agree_with_kernel_proofs(cases: ModuleType, runtime_root: Path, tmp_path: Path) -> None:
    """Every case of the module is a native record with outputs (version 5; version 6 for
    `conformance.authored_after_error`; version 7 for `conformance.authored_counters`), has resolvable
    requirements, has a phase on each error, agrees in the compiled classifier, and has a kernel
    proof of its verdict (`tests.coverage_case_support.check_coverage_cases`)."""
    check_coverage_cases(cases, runtime_root, tmp_path)
