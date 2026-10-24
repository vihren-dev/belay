"""Bounded compiler probes for S7's test-only completed-body collector."""

from dataclasses import dataclass
import json
from pathlib import Path
from typing import cast

from tests.runtime_support import CommandResult, run_command
from tests.surface_support import module_setup

Record = dict[str, str | int | None]


def payload(result: CommandResult, marker: str) -> object:
    """Read one structured experiment report, retaining compiler failures in diagnostics."""
    lines = [line.removeprefix(marker + " ") for line in result.stdout.splitlines()
             if line.startswith(marker + " ")]
    assert len(lines) == 1, result.diagnostic()
    return json.loads(lines[0])


def records(result: CommandResult) -> list[Record]:
    """Check the collector's serialized record shape before using measurements."""
    values = payload(result, "PROOF_COSTS")
    assert isinstance(values, list), result.diagnostic()
    for value in values:
        assert isinstance(value, dict), value
        for field in ("moduleName", "declaration", "status", "compiler", "scheme", "unit"):
            assert isinstance(value.get(field), str), value
        assert value.get("heartbeats") is None or isinstance(value["heartbeats"], int), value
    return cast(list[Record], values)


def counts(result: CommandResult) -> dict[str, int]:
    """Require unique, completed identities; missing measurements never become zero."""
    values = records(result)
    found: dict[str, int] = {}
    for value in values:
        name, heartbeats = value["declaration"], value["heartbeats"]
        assert isinstance(name, str) and isinstance(heartbeats, int), value
        assert value["status"] == "completed" and name not in found, value
        found[name] = heartbeats
    return found


@dataclass
class Compiler:
    """Compile isolated modules against the exact installed surface runtime."""

    runtime: Path
    directory: Path
    collector: Path

    def compile(self, name: str, source: str, *, asynchronous: bool = True,
                enabled: bool = True, imports: dict[str, Path] | None = None,
                timeout: float = 40) -> CommandResult:
        """Use ordinary Lean compilation, preserving output and a finite command timeout."""
        self.directory.mkdir(parents=True, exist_ok=True)
        path = self.directory / f"{name}.lean"
        if not enabled:
            source = source.replace("import ProofCostCollector", "import ProofCostRecords")
        path.write_text(source)
        artifact = self.directory / f"{name}.olean"
        artifact.unlink(missing_ok=True)
        setup_path = module_setup(self.runtime, self.directory)
        setup = json.loads(setup_path.read_text())
        setup["name"] = name
        extra = {"ProofCostCollector": self.collector,
                 "ProofCostRecords": self.collector.with_name("ProofCostRecords.olean"),
                 **(imports or {})}
        setup["importArts"].update({key: [[str(value)]] for key, value in extra.items()})
        setup_path.write_text(json.dumps(setup))
        return run_command([str(self.runtime / "lean/bin/lean"), f"--setup={setup_path}",
                            f"-DElab.async={str(asynchronous).lower()}",
                            f"-Dweak.proofCost.enabled={str(enabled).lower()}",
                            "-o", str(artifact), str(path)], cwd=self.directory,
                           timeout=timeout, artifacts=self.directory / "logs")

    def artifact(self, name: str) -> Path:
        """Name the compiled artifact for an explicit import mapping."""
        return self.directory / f"{name}.olean"


def checked(result: CommandResult) -> None:
    """Require successful compilation with no admitted or native-reduction proof axiom."""
    assert result.returncode == 0, result.diagnostic()
    assert all(term not in result.stdout for term in
               ("sorryAx", "ofReduceBool", "_native")), result.diagnostic()


def pair(size: int, reverse: bool = False) -> str:
    """Change actual kernel-checked proof work while keeping the cheap theorem fixed."""
    cheap = "theorem cheap : True := True.intro\n"
    costly = (f"theorem costly : (List.range {size}).length = {size} := by decide\n")
    return ("import ProofCostCollector\n" + (costly + cheap if reverse else cheap + costly)
            + "#proof_cost_records\n#proof_cost_commands\n"
              "#proof_cost_snapshot\n#print axioms cheap\n#print axioms costly\n")
