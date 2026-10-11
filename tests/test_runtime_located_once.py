"""Check that each command of `migration_check` locates the runtime once.

`Runtime.locate` checks the installation and starts `lean --version`. The
commands `verify`, `prepare` and `verify-bundle` locate it once and pass the
same runtime to `generated_inputs`.
"""

import argparse
from collections.abc import Callable
import importlib

import pytest

from migration_check.runtime import Runtime

pytestmark = [pytest.mark.unit, pytest.mark.environment]


class Stop(Exception):
    """Ends the command after input generation; later stages are not under test."""


@pytest.mark.parametrize("module,command", [("cli", "verify"), ("prepare", "prepare"), ("bundle", "verify_bundle")])
def test_command_locates_the_runtime_once(module: str, command: str, monkeypatch: pytest.MonkeyPatch) -> None:
    """The command calls `Runtime.locate` once and gives that runtime to `generated_inputs`."""
    located = object()
    calls: list[object] = []
    received: list[object] = []

    def locate() -> object:
        """Count the lookups and return a marker runtime."""
        calls.append(located)
        return located

    def generated(options: argparse.Namespace, runtime: object) -> None:
        """Record the runtime that the command passes, then stop the command."""
        received.append(runtime)
        raise Stop

    selected = importlib.import_module(f"migration_check.{module}")
    monkeypatch.setattr(Runtime, "locate", staticmethod(locate))
    monkeypatch.setattr(selected, "generated_inputs", generated)
    run: Callable[[argparse.Namespace], object] = getattr(selected, command)
    with pytest.raises(Stop):
        run(argparse.Namespace())
    assert calls == [located] and received == [located]
