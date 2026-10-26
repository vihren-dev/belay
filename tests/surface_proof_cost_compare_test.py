"""S7 proof-cost report (`ProofCostCompare.lean`, `ProofCostReport.lean`, `ProofCostArguments.lean`): the pure rules."""

from typing import cast

import pytest

from tests.proof_cost_support import Compiler, checked, compiler, payload, runtime_modules  # noqa: F401
from tests.surface_support import FIXTURES

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_comparison_report_order_and_arguments_follow_the_task_rules(compiler: Compiler) -> None:
    """`compareLibrary` accepts growth up to the allowance and not one internal unit more, lists a missing,
    failed or inexact baseline proof with its cause and never as zero, ignores unstable names and other
    compilers' counts; `comparisonExit` maps these cases to 0, 1 and 2; `LibraryCosts.ofModules` orders
    the report; `parseArguments` accepts only the documented forms. The `#guard`s of the fixture fail
    the compile when a rule is wrong."""
    result = compiler.compile("CompareChecks", (FIXTURES / "ProofCostCompareChecks.lean").read_text())
    checked(result)
    assert cast(object, payload(result, "CHECKS")) == "passed", result.diagnostic()
