"""S7 proof-cost collector (`Belay.Sqlite.ProofCost`): the option, other handlers, failures and overhead."""

from collections.abc import Callable
from typing import cast
import json
from pathlib import Path

import pytest

from tests.proof_cost_support import (ASYNCHRONOUS, COLLECTOR_IMPORT, EXPECTED, Compiler, checked,  # noqa: F401
                                      compiler, compiler_output, counts, payload, records, runtime_modules)
from tests.surface_support import FIXTURES

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@ASYNCHRONOUS
def test_option_off_and_missing_collector_change_nothing(compiler: Compiler, asynchronous: bool) -> None:
    """With the option off, or without the collector module, the compile has the same output and
    declarations as a measured one, and no records; the measured compile adds no trace line."""
    source = (FIXTURES / "ProofCostCases.lean").read_text()
    variants = {"on": source,
                "off": source.replace("belay.proofCosts true", "belay.proofCosts false", 1),
                "absent": source.replace(COLLECTOR_IMPORT, "import Belay.Sqlite.ProofCostPending\n", 1)}
    results = {name: compiler.compile("ProofCostCases", text, asynchronous=asynchronous)
               for name, text in variants.items()}
    for result in results.values():
        checked(result)
    assert records(results["off"]) == [] and records(results["absent"]) == []
    assert len(records(results["on"])) == len(EXPECTED) + 2
    outputs = {name: compiler_output(result) for name, result in results.items()}
    assert outputs["on"] == outputs["off"] == outputs["absent"], outputs
    assert "Elab.definition.value" not in outputs["on"]
    declarations = {name: payload(result, "DECLARATIONS") for name, result in results.items()}
    assert declarations["on"] == declarations["off"] == declarations["absent"]


@ASYNCHRONOUS
def test_failed_body_has_native_error_and_no_compiled_file(compiler: Compiler, asynchronous: bool) -> None:
    """A proof that fails gives the native error, no trace line and no compiled module, so the
    checker cannot read records of a module that did not compile."""
    broken = (COLLECTOR_IMPORT + "import ProofCostReader\nset_option belay.proofCosts true\n"
              "theorem broken : False := by trivial\n#proof_cost_records\n")
    measured = compiler.compile("Broken", broken, asynchronous=asynchronous)
    control = compiler.compile("Broken", broken.replace("proofCosts true", "proofCosts false"),
                               asynchronous=asynchronous)
    assert measured.returncode != 0 and control.returncode != 0
    assert not compiler.artifact("Broken").exists(), measured.diagnostic()
    assert "error" in measured.stdout and "Elab.definition.value" not in measured.stdout
    assert compiler_output(measured) == compiler_output(control)
    assert [value["status"] for value in records(measured)] == ["failed"]


def handler_source(order: tuple[str, str], option: str) -> str:
    """Two theorems, one claimed by the third-party handler, with the imports in the given order."""
    imports = {"collector": COLLECTOR_IMPORT, "other": "import ProofCostOtherHandler\n"}
    return ("".join(imports[name] for name in order) + "import ProofCostReader\n"
            f"set_option belay.proofCosts {option}\n"
            "theorem claimed_by_other : True := by trivial\n"
            "theorem ordinary : (List.range 30).length = 30 := by decide\n#proof_cost_records\n")


@ASYNCHRONOUS
@pytest.mark.parametrize("order", [("collector", "other"), ("other", "collector")],
                         ids=["other-registered-later", "other-registered-earlier"])
def test_third_party_handler_still_elaborates_its_commands(compiler: Compiler, asynchronous: bool,
                                                           order: tuple[str, str]) -> None:
    """A `declaration` handler of another library keeps its commands, whichever handler was registered
    first; the collector measures the theorem that the other handler produced, once."""
    measured = compiler.compile("Handlers", handler_source(order, "true"), asynchronous=asynchronous)
    control = compiler.compile("Handlers", handler_source(order, "false"), asynchronous=asynchronous)
    checked(measured)
    checked(control)
    assert "OTHER_HANDLER_CLAIMED" in measured.stdout
    assert compiler_output(measured) == compiler_output(control)
    assert counts(measured).keys() == {"claimed_expanded", "ordinary"}, measured.diagnostic()
    assert records(control) == []


def test_handlers_keep_incremental_elaboration(compiler: Compiler) -> None:
    """Both handlers carry the `incremental` tag, because Lean removes the snapshot context of a
    handler without it."""
    result = compiler.compile("Tags", COLLECTOR_IMPORT + "import ProofCostReader\n"
        "#proof_cost_incremental Belay.Sqlite.ProofCost.elabDeclarationMeasured\n"
        "#proof_cost_incremental Belay.Sqlite.ProofCost.elabMutualMeasured\n")
    checked(result)
    assert result.stdout.count("true") == 2 and "false" not in result.stdout, result.diagnostic()


def test_overhead_sample(compiler: Compiler, record_testsuite_property: Callable[[str, object], None]) -> None:
    """Compile three surface proof patterns with the collector on and off. The window counts go to the
    test report for the README; the test asserts that records exist, not a bound."""
    source = (FIXTURES / "ProofCostSurface.lean").read_text()
    observations: dict[str, list[dict[str, object]]] = {"off": [], "on": []}
    snapshots = []
    # The first pair warms the imports; the next four are measured in balanced order.
    for iteration, enabled in enumerate((False, True, False, True, True, False)):
        # Both texts have the same length: SQL terms record source positions.
        text = source.replace("proofCosts true", "proofCosts " + ("true " if enabled else "false"), 1)
        result = compiler.compile("Surface", text, asynchronous=False)
        checked(result)
        snapshots.append(payload(result, "DECLARATIONS"))
        window = payload(result, "WINDOW_HEARTBEATS")
        assert isinstance(window, int) and window > 0, result.diagnostic()
        if enabled:
            assert set(counts(result)) == {"constant_success", "supplied_success", "default_query"}
        if iteration >= 2:
            observations["on" if enabled else "off"].append({"window_heartbeats": window})
    first = {value["name"]: value for value in cast(list[dict[str, object]], snapshots[0])}
    for snapshot in snapshots[1:]:
        other = {value["name"]: value for value in cast(list[dict[str, object]], snapshot)}
        assert first.keys() == other.keys(), sorted(first.keys() ^ other.keys())
        assert [name for name in first if first[name] != other[name]] == []
    record_testsuite_property("proof_cost.overhead", json.dumps(observations, sort_keys=True))
    print("OVERHEAD", json.dumps(observations, sort_keys=True))


@ASYNCHRONOUS
def test_traces_that_the_user_asked_for_stay(compiler: Compiler, asynchronous: bool) -> None:
    """The collector removes only its own trace nodes: a trace class that the user enabled and Lean recorded
    inside a measured body appears as it does without the collector."""
    source = (COLLECTOR_IMPORT + "import ProofCostReader\nset_option belay.proofCosts true\n"
              "set_option trace.Meta.Tactic.simp.rewrite true in\ntheorem usesSimp : [1, 2].length = 2 := by simp\n"
              "theorem plain : True := trivial\n")
    measured = compiler.compile("Traces", source, asynchronous=asynchronous)
    control = compiler.compile("Traces", source.replace("proofCosts true", "proofCosts false"), asynchronous=asynchronous)
    checked(measured)
    checked(control)
    assert "Meta.Tactic.simp.rewrite" in control.stdout
    assert measured.stdout == control.stdout
