"""S7 proof-cost collector (`Belay.Sqlite.ProofCost`): records, coverage, bypass and coexistence."""

from collections.abc import Callable
from decimal import Decimal
import json
from pathlib import Path
from typing import cast

import pytest

from tests.proof_cost_support import (COLLECTOR_IMPORT, Compiler, READER_IMPORT, checked, compiler_output,
                                      counts, payload, records)
from tests.runtime_support import CommandResult
from tests.surface_support import FIXTURES

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

ASYNCHRONOUS = pytest.mark.parametrize("asynchronous", [True, False], ids=["async", "sync"])
"""Lean elaborates proofs in the background (`Elab.async`) or in the command; both are measured."""


@pytest.fixture(scope="module")
def runtime_modules(runtime_root: Path, tmp_path_factory: pytest.TempPathFactory) -> dict[str, Path]:
    """Compile the reader and the third-party handler fixtures once; tests import them by name."""
    compiler = Compiler(runtime_root, tmp_path_factory.mktemp("proof-cost-fixtures"))
    for name in ("ProofCostReader", "ProofCostOtherHandler"):
        checked(compiler.compile_fixture(name))
    return dict(compiler.modules)


@pytest.fixture
def compiler(runtime_root: Path, tmp_path: Path, runtime_modules: dict[str, Path]) -> Compiler:
    """A compiler whose modules include the reader and the third-party handler."""
    return Compiler(runtime_root, tmp_path, dict(runtime_modules))


def pair(size: int, *, reverse: bool = False, mutual: bool = False, extra: str = "") -> str:
    """A cheap and a costly theorem, in the given order, alone or in one mutual block."""
    cheap = "theorem cheap : True := True.intro\n"
    costly = f"theorem costly : (List.range {size}).length = {size} := by decide\n"
    body = costly + cheap if reverse else cheap + costly
    return (COLLECTOR_IMPORT + "import ProofCostReader\nset_option belay.proofCosts true\n" + extra
            + ("mutual\n" + body + "end\n" if mutual else body) + "#proof_cost_records\n")


@ASYNCHRONOUS
@pytest.mark.parametrize("mutual", [False, True], ids=["plain", "mutual"])
def test_growth_shows_on_its_own_theorem(compiler: Compiler, asynchronous: bool, mutual: bool,
                                         record_testsuite_property: Callable[[str, object], None]) -> None:
    """The collector attributes cost to the right theorem in both orders, and in a `mutual` block."""
    observations = []
    for size, reverse in ((30, False), (30, True), (100, False)):
        result = compiler.compile("Pair", pair(size, reverse=reverse, mutual=mutual), asynchronous=asynchronous)
        checked(result)
        measured = counts(result)
        assert measured.keys() == {"cheap", "costly"}, result.diagnostic()
        assert measured["costly"] > 10 * measured["cheap"] > 0, measured
        scheme = f"proof-body-v1-{'async' if asynchronous else 'sync'}"
        assert {value["scheme"] for value in records(result)} == {scheme}
        observations.append(measured)
    assert observations[-1]["costly"] > 2 * max(value["costly"] for value in observations[:-1]), observations
    assert observations[-1]["cheap"] < observations[-1]["costly"] / 10, observations
    record_testsuite_property(f"proof_cost.attribution.{asynchronous}.{mutual}", json.dumps(observations))
    print("BUDGET_UNITS", {name: str(Decimal(value) / 1000) for name, value in observations[0].items()})


def test_option_works_from_the_command_line(compiler: Compiler) -> None:
    """The `weak.` form of the option, which a Lake library sets for all its modules, turns collection on
    for a module that does not call `set_option`; with the value false it stays off."""
    source = pair(30).replace("set_option belay.proofCosts true\n", "")
    measured = compiler.compile("Weak", source, weak_option=True)
    checked(measured)
    assert counts(measured).keys() == {"cheap", "costly"}, measured.diagnostic()
    off = compiler.compile("Weak", source, weak_option=False)
    checked(off)
    assert records(off) == []


EXPECTED = {
    "Coverage.tactic": ("thm", "stable"), "Coverage.term": ("thm", "stable"),
    "Coverage.proofDefinition": ("proofDefinition", "stable"),
    "Coverage.recursive": ("thm", "stable"), "Coverage.withWhere": ("thm", "stable"),
    "Coverage.fromMacro": ("thm", "stable"),
    "Coverage.evenPeer": ("thm", "stable"), "Coverage.oddPeer": ("thm", "stable"),
    "Coverage.mutualProofOne": ("proofDefinition", "stable"),
    "Coverage.mutualProofTwo": ("proofDefinition", "stable"),
    "_private.ProofCostCases.0.Coverage.hidden": ("thm", "privateName"),
}
"""The named proofs of `ProofCostCases.lean`, with their kind and identity. Four more records are
anonymous examples; a predicate, a data definition, an embedded proof and a theorem with the
option off have none."""


@ASYNCHRONOUS
def test_coverage_table(compiler: Compiler, asynchronous: bool) -> None:
    """The collector records each named proof of the fixture once, with its kind and identity."""
    source = (FIXTURES / "ProofCostCases.lean").read_text()
    result = compiler.compile("ProofCostCases", source, asynchronous=asynchronous)
    checked(result)
    found = {str(value["declaration"]): (value["kind"], value["identity"]) for value in records(result)}
    examples = {name for name in found if name.startswith("Coverage._example@")}
    assert len(examples) == 2 and all(found[name] == ("anonymousExample", "anonymous") for name in examples)
    assert {name: found[name] for name in found if name not in examples} == EXPECTED, result.diagnostic()
    assert len(counts(result)) == len(EXPECTED) + 2
    assert result.stdout.count("does not depend on any axioms") == 3, result.diagnostic()


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


def identities(result: CommandResult) -> list[tuple[object, ...]]:
    """What names a record, without the count, which varies between compiles."""
    return [(value["module"], value["declaration"], value["kind"], value["scheme"], value["sourceHash"])
            for value in records(result)]


def test_records_survive_import_diamond_and_relocation(runtime_root: Path, tmp_path: Path,
                                                       runtime_modules: dict[str, Path]) -> None:
    """The records are in the compiled module: a module that imports it by two paths shows each record
    once, the source file is not needed, and a recompile in another folder keeps the identities."""
    first = Compiler(runtime_root, tmp_path / "first", dict(runtime_modules))
    original = first.compile("Pair", pair(30))
    checked(original)
    (first.directory / "Pair.lean").unlink()
    for name in ("Left", "Right"):
        checked(first.compile(name, "import Pair\n"))
    reader = "import Left\nimport Right\nimport ProofCostReader\n#proof_cost_records\n"
    read = first.compile("Reader", reader)
    checked(read)
    assert records(read) == records(original)
    other = Compiler(runtime_root, tmp_path / "relocated", dict(runtime_modules))
    relocated = other.compile("Pair", pair(30))
    checked(relocated)
    assert identities(relocated) == identities(original)


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


def test_float_edges_of_the_trace_reader(compiler: Compiler) -> None:
    """`exactCount` and `bodyNodes` (`ProofCostTrace.lean`) turn only exactly representable counters
    into counts; a zero count is a completed zero and an inexact one is not a count."""
    result = compiler.compile("Edges", (FIXTURES / "ProofCostTraceChecks.lean").read_text())
    checked(result)
    assert cast(object, payload(result, "EDGES")) == "passed", result.diagnostic()
