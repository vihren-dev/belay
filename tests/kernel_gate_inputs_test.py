"""The `.olean` gate checks the generated inputs against its own resolution of the record.

`ProofChecker.lean` resolves the structural record again (`GateInputs.lean`) and
rejects a compiled generated declaration, or a record, whose resolution differs.
"""

import pytest

from tests.kernel_gate_test import RECORD, KernelCase, compiled_kernel, kernel, source  # noqa: F401  (fixtures)

pytestmark = [pytest.mark.integration, pytest.mark.kernel, pytest.mark.requires_lean]


@pytest.mark.parametrize("module,old,new,name", [
    ("SchemaInputs", '"3.51.0" "2025', '"3.46.0" "2025', "Generated.profile"),
    ("SchemaInputs", "def startCatalog : Catalog := []",
     'def startCatalog : Catalog := [{ name := "t", entry := .table { columns := [{ name := "a", declaredType := none }] } }]',
     "Generated.startCatalog"),
    ("SqlInputs", "def resolved : List Resolved.Statement := []", "def resolved : List Resolved.Statement := [.begin]",
     "Generated.resolved"),
    ("SqlInputs", "def nextCatalog : Catalog := []",
     'def nextCatalog : Catalog := [{ name := "t", entry := .table { columns := [{ name := "a", declaredType := none }] } }]',
     "Generated.nextCatalog"),
], ids=["profile", "start_catalog", "resolved", "next_catalog"])
def test_changed_generated_declaration(kernel: KernelCase, module: str, old: str, new: str, name: str) -> None:
    """A compiled generated declaration that differs from the gate's own resolution of the record is rejected."""
    assert old in source(module)
    kernel.compile("trusted", module, source(module).replace(old, new))
    if module == "SchemaInputs":
        for dependent in ("SqlInputs", "Interpretation"):
            kernel.compile("trusted", dependent, source(dependent))
    result = kernel.check()
    assert result.returncode == 1, result.diagnostic()
    assert f"differs from the resolution of the script record: {name}" in result.stderr, result.diagnostic()


def test_changed_record(kernel: KernelCase) -> None:
    """A record whose resolution differs from the compiled inputs is rejected, as is one that does not resolve."""
    changed = kernel.check(record={**RECORD, "script": ["begin"]})
    assert changed.returncode == 1 and "Generated.script" in changed.stderr, changed.diagnostic()
    restricted = kernel.check(record={**RECORD, "script": [{"createIndex": {"name": "i", "unique": False,
                                                                            "table": "t", "columns": ["a"]}}]})
    assert restricted.returncode == 1 and "does not resolve" in restricted.stderr, restricted.diagnostic()
