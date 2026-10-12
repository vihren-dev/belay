"""Shared example cases and paths for the ADR 0003 latency experiments."""

from dataclasses import dataclass
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
"""Repository root; the experiments use its checkout runtime (`just build`)."""

sys.path.insert(0, str(ROOT))
from migration_check.project_config import ProjectConfig, load  # noqa: E402

WORK = ROOT / "build" / "adr-0003-latency"
"""Scratch outputs: compiled examples, exports and the cloned exporter."""


@dataclass(frozen=True)
class ExampleCase:
    """One checked-in example, with the inputs that its `belay.toml` names."""

    name: str
    config: ProjectConfig

    @property
    def schema(self) -> Path:
        """Starting schema SQL."""
        return self.config.schema

    @property
    def approved(self) -> Path:
        """Folder of the approved contract."""
        return self.config.contract

    @property
    def candidate(self) -> Path:
        """Folder of the candidate modules and the migration."""
        return self.config.proofs

    @property
    def profile(self) -> str:
        """SQLite profile."""
        return self.config.profile

    @property
    def theorem(self) -> str:
        """The proved root: a refutation proves `migrationViolated`."""
        return "Proofs.migrationViolated" if self.config.test_status == "VIOLATED" else "Proofs.migrationCorrect"

    def verify_arguments(self) -> list[str]:
        """Public `migration-check verify` arguments for this example."""
        return ["verify", "--format", "json", *self.config.contract_arguments(), *self.config.candidate_arguments()]


EXAMPLES = ROOT / "examples"
"""The folder that holds the checked-in cases."""

CASES = tuple(ExampleCase(name, load(EXAMPLES / folder / "belay.toml", EXAMPLES)) for name, folder in (
    ("small", "add_column_then_table"), ("refutation", "missing_required_column"), ("atuin", "atuin")))
"""The three examples of the latency experiments, by their names in the recorded results."""
