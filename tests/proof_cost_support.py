"""Bounded compiler runs for the S7 proof-cost tests: fixtures are compiled against the installed surface."""

from dataclasses import dataclass, field
import json
from pathlib import Path
from typing import cast

from tests.runtime_support import CommandResult, run_command
from tests.surface_support import FIXTURES, module_setup

Record = dict[str, str | int | None]

MARKERS = ("PROOF_COSTS", "DECLARATIONS", "WINDOW_HEARTBEATS", "INCREMENTAL")
"""The first words of the lines that the reader fixture prints; they are not compiler output."""
COLLECTOR_IMPORT = "import Belay.Sqlite.ProofCost\n"
"""The line that installs the collector."""
READER_IMPORT = "import Belay.Sqlite.ProofCostPending\nimport ProofCostReader\n"
"""The lines of a control compile: the reader and the data module, without the handlers."""


def payload(result: CommandResult, marker: str) -> object:
    """Read the one JSON report that the reader fixture printed after `marker`."""
    lines = [line.removeprefix(marker + " ") for line in result.stdout.splitlines()
             if line.startswith(marker + " ")]
    assert len(lines) == 1, result.diagnostic()
    return json.loads(lines[0])


def records(result: CommandResult) -> list[Record]:
    """The printed records, after a check of the field types that the checker relies on."""
    values = payload(result, "PROOF_COSTS")
    assert isinstance(values, list), result.diagnostic()
    for value in values:
        assert isinstance(value, dict), value
        for name in ("module", "declaration", "kind", "identity", "status", "unit", "compiler",
                     "scheme", "sourceHash"):
            assert isinstance(value.get(name), str), value
        assert value.get("heartbeats") is None or isinstance(value["heartbeats"], int), value
    return cast(list[Record], values)


def counts(result: CommandResult) -> dict[str, int]:
    """The completed counts by declaration; a repeated name or a missing count fails the test."""
    found: dict[str, int] = {}
    for value in records(result):
        name, heartbeats = value["declaration"], value["heartbeats"]
        assert isinstance(name, str) and isinstance(heartbeats, int), value
        assert value["status"] == "completed" and name not in found, value
        found[name] = heartbeats
    return found


def compiler_output(result: CommandResult) -> str:
    """The messages of the compiler: the output without the lines of the reader fixture."""
    return "\n".join(line for line in result.stdout.splitlines()
                     if not line.startswith(MARKERS))


def checked(result: CommandResult) -> None:
    """Require a successful compile with no admitted or native-reduction axiom."""
    assert result.returncode == 0, result.diagnostic()
    assert all(term not in result.stdout for term in
               ("sorryAx", "ofReduceBool", "_native")), result.diagnostic()


@dataclass
class Compiler:
    """Compile isolated modules with the installed `lean`, against the installed surface runtime."""

    runtime: Path
    directory: Path
    modules: dict[str, Path] = field(default_factory=dict)
    """The compiled modules that the next compile can import, by module name."""

    def compile(self, name: str, source: str, *, asynchronous: bool = True,
                weak_option: bool | None = None, automatic_check: bool = False,
                timeout: float = 90) -> CommandResult:
        """Compile `source` as module `name`; on success the module can be imported afterwards. The
        automatic SQL check (S5) is off unless `automatic_check` is set."""
        self.directory.mkdir(parents=True, exist_ok=True)
        path = self.directory / f"{name}.lean"
        path.write_text(source)
        artifact = self.artifact(name)
        artifact.unlink(missing_ok=True)
        setup_path = module_setup(self.runtime, self.directory, automatic_check=automatic_check)
        setup = json.loads(setup_path.read_text())
        setup["name"] = name
        setup["importArts"].update({key: [[str(value)]] for key, value in self.modules.items()})
        setup_path.write_text(json.dumps(setup))
        options = [] if weak_option is None else [f"-Dweak.belay.proofCosts={str(weak_option).lower()}"]
        result = run_command([str(self.runtime / "lean/bin/lean"), f"--setup={setup_path}",
                              f"-DElab.async={str(asynchronous).lower()}", *options,
                              "-o", str(artifact), str(path)], cwd=self.directory,
                             timeout=timeout, artifacts=self.directory / "logs")
        if result.returncode == 0:
            self.modules[name] = artifact
        return result

    def compile_fixture(self, name: str) -> CommandResult:
        """Compile the Lean file `tests/surface/NAME.lean` as module NAME."""
        return self.compile(name, (FIXTURES / f"{name}.lean").read_text())

    def artifact(self, name: str) -> Path:
        """The compiled file of a module, which exists only after a successful compile."""
        return self.directory / f"{name}.olean"
