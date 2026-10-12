"""Read a project configuration file, `belay.toml` (ADR 0010 section 7).

A verification case in this repository is a folder with a `belay.toml` that
names its inputs, so tests and experiments use the input format of a user's
project instead of paths written in code. The command line tool reads the same
file in a later change. Only the standard library is used, so test targets that
run the installed tool can import this module without the rest of the package.

Format:

    [project]
    profile = "3.51.0"                       # SQLite semantic version
    schema = "../approved/schema.sql"        # starting schema SQL
    migration = "migration.sql"              # candidate migration SQL
    contract = "../approved"                 # Requirements.lean, Interpretation.lean
    baseline = "../approved/baseline.json"   # optional approval baseline
    proofs = "."                             # folder of the candidate modules
    proof_modules = ["NextInterpretation", "Proofs"]

    [test]                                   # read only by tests
    status = "VERIFIED"                      # expected status of the unchanged case
    suite = "cli"                            # Nix test target that verifies it

Paths are relative to the file. They may leave the case folder, but not the
folder that holds the cases (`root`), because several cases share one contract.
"""

from dataclasses import dataclass
from pathlib import Path
import tomllib

CONFIG_NAME = "belay.toml"
"""File name of a project configuration."""

REQUIRED_PROOF_MODULES = ("NextInterpretation", "Proofs")
"""Candidate modules that every project has; others are helpers."""

PROJECT_KEYS = frozenset({"profile", "schema", "migration", "contract", "baseline", "proofs", "proof_modules"})
"""Keys allowed in `[project]`; an unknown key is an error, so a typo cannot pass silently."""

TEST_KEYS = frozenset({"status", "suite"})
"""Keys allowed in `[test]`."""

STATUSES = frozenset({"VERIFIED", "VIOLATED", "UNVERIFIED", "INPUT_ERROR", "UNSUPPORTED"})
"""Statuses a test may expect; the same set the command line reports."""


class ConfigError(ValueError):
    """A configuration file that cannot be used; the message names the file and the field."""

    def __init__(self, file: Path, field: str, problem: str) -> None:
        super().__init__(f"{file}: field {field}: {problem}. Correct {field} in {file}.")


@dataclass(frozen=True)
class ProjectConfig:
    """The validated inputs of one project, with absolute paths."""

    file: Path
    profile: str
    schema: Path
    migration: Path
    contract: Path
    baseline: Path | None
    proofs: Path
    proof_modules: tuple[str, ...]
    test_status: str | None
    test_suite: str

    @property
    def requirements(self) -> Path:
        """The approved requirements module."""
        return self.contract / "Requirements.lean"

    @property
    def interpretation(self) -> Path:
        """The approved interpretation module."""
        return self.contract / "Interpretation.lean"

    def contract_arguments(self) -> list[str]:
        """Command line inputs shared by `verify`, `prepare` and `verify-bundle`."""
        return ["--profile", self.profile, "--schema", str(self.schema), "--requirements", str(self.requirements),
                "--interpretation", str(self.interpretation), "--migration", str(self.migration)]

    def candidate_arguments(self) -> list[str]:
        """Command line inputs of `verify` and `prepare` that name the candidate modules."""
        return ["--next-interpretation", str(self.proofs / "NextInterpretation.lean"),
                "--proofs", str(self.proofs / "Proofs.lean")]


def text(table: dict[str, object], key: str, file: Path, section: str) -> str:
    """A required non-empty string field."""
    value = table.get(key)
    if not isinstance(value, str) or not value:
        raise ConfigError(file, f"{section}.{key}", "a non-empty string is required")
    return value


def inside(file: Path, root: Path, key: str, relative: str, *, directory: bool) -> Path:
    """Resolve a path field and require that it exists inside `root`."""
    path = (file.parent / relative).resolve()
    if not path.is_relative_to(root.resolve()):
        raise ConfigError(file, f"project.{key}", f"{relative} is outside {root}")
    if not (path.is_dir() if directory else path.is_file()):
        raise ConfigError(file, f"project.{key}", f"{relative} is not an existing {'folder' if directory else 'file'}")
    return path


def proof_modules(project: dict[str, object], file: Path, proofs: Path) -> tuple[str, ...]:
    """The candidate module names; each needs a source file in the proofs folder."""
    value = project.get("proof_modules")
    if not isinstance(value, list) or not value or not all(isinstance(name, str) and name for name in value):
        raise ConfigError(file, "project.proof_modules", "a non-empty list of module names is required")
    for name in [*REQUIRED_PROOF_MODULES, *value]:
        if name not in value:
            raise ConfigError(file, "project.proof_modules", f"{name} is required")
        if not (proofs / f"{name}.lean").is_file():
            raise ConfigError(file, "project.proof_modules", f"{name}.lean is missing in {proofs}")
    return tuple(value)


def load(file: Path, root: Path) -> ProjectConfig:
    """Read and validate one `belay.toml` whose paths must stay inside `root`."""
    try:
        data = tomllib.loads(file.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as error:
        raise ConfigError(file, "(file)", f"not valid TOML ({error})") from error
    unknown_tables = set(data) - {"project", "test"}
    project, test = data.get("project"), data.get("test", {})
    if unknown_tables or not isinstance(project, dict) or not isinstance(test, dict):
        raise ConfigError(file, "(tables)", "only the tables [project] and [test] are allowed, and [project] is required")
    for key in set(project) - PROJECT_KEYS:
        raise ConfigError(file, f"project.{key}", "unknown field")
    for key in set(test) - TEST_KEYS:
        raise ConfigError(file, f"test.{key}", "unknown field")
    contract = inside(file, root, "contract", text(project, "contract", file, "project"), directory=True)
    for module in ("Requirements", "Interpretation"):
        if not (contract / f"{module}.lean").is_file():
            raise ConfigError(file, "project.contract", f"{module}.lean is missing in {contract}")
    proofs = inside(file, root, "proofs", text({"proofs": project.get("proofs", ".")}, "proofs", file, "project"),
                    directory=True)
    baseline = (inside(file, root, "baseline", text(project, "baseline", file, "project"), directory=False)
                if "baseline" in project else None)
    status = test.get("status")
    if status is not None and status not in STATUSES:
        raise ConfigError(file, "test.status", f"one of {', '.join(sorted(STATUSES))} is required")
    return ProjectConfig(
        file=file.resolve(), profile=text(project, "profile", file, "project"),
        schema=inside(file, root, "schema", text(project, "schema", file, "project"), directory=False),
        migration=inside(file, root, "migration", text(project, "migration", file, "project"), directory=False),
        contract=contract, baseline=baseline, proofs=proofs,
        proof_modules=proof_modules(project, file, proofs), test_status=status,
        test_suite=text({"suite": test.get("suite", "cli")}, "suite", file, "test"))


def discover(root: Path) -> list[Path]:
    """Every `belay.toml` below `root`, in a stable order."""
    return sorted(root.rglob(CONFIG_NAME))
