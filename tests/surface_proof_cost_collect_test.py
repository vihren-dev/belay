"""S7 proof-cost collector (`Belay.Sqlite.ProofCost`): records, attribution, coverage and persistence."""

from collections.abc import Callable
from decimal import Decimal
import json
from pathlib import Path
from typing import cast

import pytest

from tests.proof_cost_support import (ASYNCHRONOUS, COLLECTOR_IMPORT, EXPECTED, Compiler, checked,  # noqa: F401
                                      compiler, counts, pair, payload, records, runtime_modules)
from tests.runtime_support import CommandResult
from tests.surface_support import FIXTURES

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


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


def test_float_edges_of_the_trace_reader(compiler: Compiler) -> None:
    """`exactCount` and `bodyNodes` (`ProofCostTrace.lean`) turn only exactly representable counters
    into counts; a zero count is a completed zero and an inexact one is not a count."""
    result = compiler.compile("Edges", (FIXTURES / "ProofCostTraceChecks.lean").read_text())
    checked(result)
    assert cast(object, payload(result, "EDGES")) == "passed", result.diagnostic()
