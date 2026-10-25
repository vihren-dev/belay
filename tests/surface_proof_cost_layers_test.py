"""Layer rule 7 (ADR 0017, S7): `import Belay` does not import the proof-cost collector.

The collector installs command handlers, so a user imports `Belay.Sqlite.ProofCost` to opt in. The
other rules are in `surface_layers_test.py`."""

import pytest

from tests.surface_layers_test import SURFACE, import_closure, imports, lean_files, module_name

pytestmark = pytest.mark.unit

COLLECTOR_MODULE = "Belay.Sqlite.ProofCost"
"""The module that registers the handlers of the collector."""


def test_import_belay_does_not_install_the_proof_cost_collector() -> None:
    """The import closure of the `Belay` root, read from the import lines, does not contain the collector."""
    dependencies = {module_name(SURFACE, path): imports(path)
                    for path in lean_files(SURFACE) if path.name != "lakefile.lean"}
    assert {"Belay", COLLECTOR_MODULE} <= dependencies.keys()
    assert COLLECTOR_MODULE not in import_closure("Belay", dependencies)
