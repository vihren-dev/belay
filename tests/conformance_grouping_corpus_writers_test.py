"""The corpus writers of the authored cases of conditional creation and grouping (ADR 0030).

`conformance.conditional_creation_evidence`, `conformance.group_value_evidence` and
`conformance.expression_grouping_evidence` record their cases natively and publish them through
`conformance.authored_evidence.publish`. A round trip writes a new corpus, reads it back
unchanged, replays it natively and refuses to replace it. Like the other writers
(`tests/conformance_corpus_writers_test.py`), they run in the scheduled suite `writers`.
"""

from pathlib import Path
from types import ModuleType

import pytest

from conformance import (authored_conditional_creation, authored_expression_grouping, authored_group_values,
                         conditional_creation_evidence, expression_grouping_evidence, group_value_evidence)
from conformance.corpus import load

pytestmark = [pytest.mark.integration, pytest.mark.conformance,
              pytest.mark.requires_native("translation-program", "sqlite3")]


@pytest.mark.parametrize(("evidence", "cases", "count", "version"), [
    (conditional_creation_evidence, authored_conditional_creation, len(authored_conditional_creation.definitions()), 56),
    (group_value_evidence, authored_group_values, len(authored_group_values.definitions()), 57),
    (expression_grouping_evidence, authored_expression_grouping,
     len(authored_expression_grouping.definitions()) + len(authored_expression_grouping.date_cases()), 58)],
    ids=["conditional-creation", "group-values", "expression-grouping"])
def test_grouping_corpus_round_trips(tmp_path: Path, evidence: ModuleType, cases: ModuleType, count: int,
                                     version: int) -> None:
    """Each writer publishes its corpus version of version 7 records, one for each case of its
    module, which reads back unchanged and replays natively, and refuses to replace an existing
    directory."""
    assert evidence.CORPUS.records is cases.records
    manifest = evidence.publish(tmp_path / "corpus")
    assert manifest["nativeVersion"] == 7 and manifest["corpusVersion"] == version
    assert manifest["recordedCases"] == count
    assert load(tmp_path / "corpus")[0] == manifest
    with pytest.raises(ValueError, match="already exists"):
        evidence.publish(tmp_path / "corpus")
