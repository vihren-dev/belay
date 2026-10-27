"""The table rebuild of the guide: tactic rules for schema statements and the three claims about the rebuild
(ADR 0017, S6, part 2)."""

from pathlib import Path

import pytest

from tests.surface_assertion_examples_test import check_module_chain

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

CHAIN_TIMEOUT_SECONDS = 400
"""The time limit of one fixture module, in seconds."""


def test_sql_run_rules_for_schema_and_transaction_statements(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_run` applies its rules for CREATE TABLE, DROP TABLE, a rename, a pragma setting, BEGIN and COMMIT
    (the modules SchemaStepRules and ControlStepRules) to one program on a database with the schema of the
    guide, for every complete environment. The fixture SchemaRuleExamples closes every premise except the final
    claim, which says that the program leaves no open transaction and foreign keys on, and uses only logical
    axioms."""
    check_module_chain(runtime_root, tmp_path, (("RebuildGuide", 0), ("SchemaRuleExamples", 1)),
                       timeout=CHAIN_TIMEOUT_SECONDS)
