"""Check that `migration_check` checks the installation once for each command.

`Runtime.locate` checks the installation and starts `lean --version`.
`generated_inputs` locates the runtime after it checks the profile, and the
commands `verify`, `prepare` and `verify-bundle` use the runtime from its
result instead of locating it again.
"""

import argparse
from collections.abc import Callable
import importlib
from types import SimpleNamespace

import pytest

from belay.sqlite.errors import SqlError
from migration_check.inputs import generated_inputs
from migration_check.runtime import Runtime

pytestmark = [pytest.mark.unit, pytest.mark.environment]


class Stop(Exception):
    """Ends the command at its first use of the runtime; later stages are not under test."""


class StopRuntime:
    """A located runtime whose first use ends the test."""

    def __getattr__(self, name: str) -> object:
        """Stop at the first attribute that the caller reads."""
        raise Stop(name)


@pytest.mark.parametrize("module,command", [("cli", "verify"), ("prepare", "prepare"), ("bundle", "verify_bundle")])
def test_command_uses_the_runtime_from_input_generation(module: str, command: str,
                                                        monkeypatch: pytest.MonkeyPatch) -> None:
    """The command does not call `Runtime.locate` itself; it uses `GeneratedInputs.runtime`."""
    def located_twice() -> object:
        """Fail the test when the command locates the runtime again."""
        raise AssertionError("runtime located again")

    def generated(options: argparse.Namespace) -> SimpleNamespace:
        """Return generated inputs that carry a runtime, with the fields `verify` reads first."""
        return SimpleNamespace(runtime=StopRuntime(), schema_hash="", schema_source="", sql_source="")

    selected = importlib.import_module(f"migration_check.{module}")
    monkeypatch.setattr(Runtime, "locate", staticmethod(located_twice))
    monkeypatch.setattr(selected, "generated_inputs", generated)
    run: Callable[[argparse.Namespace], object] = getattr(selected, command)
    with pytest.raises(Stop):
        run(argparse.Namespace(artifacts=None))


def test_profile_is_checked_before_the_runtime(monkeypatch: pytest.MonkeyPatch) -> None:
    """An invalid profile is an input error even when the runtime cannot be located."""
    def unavailable() -> object:
        """Fail the test when the runtime is located before the profile check."""
        raise AssertionError("runtime located before the profile check")

    monkeypatch.setattr(Runtime, "locate", staticmethod(unavailable))
    with pytest.raises(SqlError) as refused:
        generated_inputs(argparse.Namespace(profile="invalid"))
    assert refused.value.status == "INPUT_ERROR"


def test_input_generation_locates_the_runtime_once(monkeypatch: pytest.MonkeyPatch) -> None:
    """`generated_inputs` locates the runtime once, after the profile check."""
    calls: list[str] = []

    def locate() -> StopRuntime:
        """Count the lookups and return a runtime that stops at its first use."""
        calls.append("locate")
        return StopRuntime()

    monkeypatch.setattr(Runtime, "locate", staticmethod(locate))
    with pytest.raises(Stop):
        generated_inputs(argparse.Namespace(profile="3.51.0"))
    assert calls == ["locate"]
