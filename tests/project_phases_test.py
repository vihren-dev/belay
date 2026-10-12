"""The proof author's phases through the public launcher: generate, check and audit (ADR 0010 section 10).

The audit gives, in the agent's own build, the reasons the verifier would reject a
bundle; generation never causes a rebuild by itself; a lakefile that turns off
kernel checking is refused before Lake runs.
"""

from collections.abc import Callable
from pathlib import Path

import pytest

from migration_check.project_config import ProjectConfig, load
from tests.runtime_support import CommandResult

pytestmark = [pytest.mark.e2e, pytest.mark.requires_lean, pytest.mark.requires_native]

HEADER = "import Generated\nimport SqliteVerifier.Demonstration\n\n"
"""The small example's imports."""

PROOFS = {
    "correct": None,
    "sorry": HEADER + "namespace Proofs\ntheorem migrationCorrect : Generated.expected := by sorry\nend Proofs\n",
    "own_axiom": HEADER + "axiom cheat : False\nnamespace Proofs\n"
                 "theorem migrationCorrect : Generated.expected := cheat.elim\nend Proofs\n",
    "outside_import": "import Lake\n" + HEADER + "namespace Proofs\ntheorem migrationCorrect : Generated.expected :=\n"
                      "  SqliteVerifier.Demonstration.migrationCorrect\nend Proofs\n",
}
"""`Proofs.lean` variants; each but the first breaks one audit rule."""

CAUSES = {"correct": None, "sorry": "sorryAx", "own_axiom": "cheat", "outside_import": "Lake"}
"""What the audit's message names for each variant."""


@pytest.fixture
def phase(runtime_root: Path, tmp_path: Path, command_runner: Callable[..., CommandResult]
          ) -> Callable[..., dict[str, object]]:
    """Run one proof-author command with JSON output and return its report."""
    def run(*arguments: str) -> dict[str, object]:
        """The command's JSON report."""
        result = command_runner([str(runtime_root / "bin/migration-check"), *arguments, "--format", "json"],
                                cwd=tmp_path, timeout=180)
        return result.json_object()
    return run


@pytest.fixture
def small(example_factory: Callable[[str], Path]) -> ProjectConfig:
    """A private copy of the small example's proofs project."""
    examples = example_factory(".")
    return load(examples / "add_column_then_table/belay.toml", examples)


@pytest.mark.parametrize("variant", PROOFS)
def test_audit_names_the_cause(variant: str, small: ProjectConfig, phase: Callable[..., dict[str, object]]) -> None:
    """After `generate` and `check`, `audit` accepts the correct proof and rejects `sorry`, an own axiom and an
    import of a module the verifier does not have, naming each."""
    if PROOFS[variant] is not None:
        (small.proofs / "Proofs.lean").write_text(PROOFS[variant])
    project = ["--project", str(small.proofs)]
    assert phase("generate", *small.contract_arguments(), *project)["status"] == "GENERATED"
    assert phase("check", *project)["status"] == "CHECKED"
    report = phase("audit", *project)
    if CAUSES[variant] is None:
        assert report["status"] == "AUDITED", report
    else:
        assert report["status"] == "UNVERIFIED" and CAUSES[variant] in str(report["message"]), report


def test_generate_is_stable(small: ProjectConfig, phase: Callable[..., dict[str, object]]) -> None:
    """A second `generate` with the same inputs writes no file, so it never makes Lake rebuild."""
    arguments = [*small.contract_arguments(), "--project", str(small.proofs)]
    first, second = phase("generate", *arguments), phase("generate", *arguments)
    assert set(first["written_modules"]) == {"SchemaInputs", "SqlInputs", "Generated", "Check"}, first
    assert second["written_modules"] == [], second


def test_lakefile_that_skips_kernel_checks_is_refused(small: ProjectConfig,
                                                      phase: Callable[..., dict[str, object]]) -> None:
    """`generate` refuses a lakefile that sets `debug.skipKernelTC`, which the audit could not see."""
    lakefile = small.proofs / "lakefile.toml"
    lakefile.write_text(lakefile.read_text().replace('restoreAllArtifacts = true\n',
        'restoreAllArtifacts = true\nmoreLeanArgs = ["-Ddebug.skipKernelTC=true"]\n', 1))
    report = phase("generate", *small.contract_arguments(), "--project", str(small.proofs))
    assert report["status"] == "INPUT_ERROR" and "debug.skipKernelTC" in str(report["message"]), report


def test_prepare_audits_before_it_exports(small: ProjectConfig, phase: Callable[..., dict[str, object]],
                                          tmp_path: Path) -> None:
    """`prepare` runs the audit before the export, so a proof with `sorry` gives no bundle; `export` alone would
    write one for `verify-bundle` to reject."""
    (small.proofs / "Proofs.lean").write_text(PROOFS["sorry"])
    bundle = tmp_path / "proof.bundle"
    report = phase("prepare", *small.contract_arguments(), "--project", str(small.proofs), "--output", str(bundle))
    assert report["status"] == "UNVERIFIED" and "sorryAx" in str(report["message"]), report
    assert not bundle.exists()


def test_export_builds_the_current_sources(small: ProjectConfig, phase: Callable[..., dict[str, object]],
                                           tmp_path: Path) -> None:
    """`export` builds before it exports: after a proof edit without `check`, the bundle holds the edited proof,
    so `verify-bundle` judges what the author wrote, not a stale build."""
    project = [*small.contract_arguments(), "--project", str(small.proofs)]
    assert phase("generate", *project)["status"] == "GENERATED"
    assert phase("check", "--project", str(small.proofs))["status"] == "CHECKED"
    (small.proofs / "Proofs.lean").write_text("import Generated\ntheorem Proofs.migrationCorrect : True := trivial\n")
    bundle = tmp_path / "proof.bundle"
    assert phase("export", *project, "--output", str(bundle))["status"] == "PREPARED"
    report = phase("verify-bundle", *small.contract_arguments(), "--bundle", str(bundle))
    assert report["status"] == "UNVERIFIED" and "reconstructed verification target" in str(report["message"]), report


def test_compile_error_names_the_module(small: ProjectConfig, phase: Callable[..., dict[str, object]],
                                        tmp_path: Path) -> None:
    """A type error in a proof module gives UNVERIFIED from `prepare`, naming the module, as before Lake."""
    (small.proofs / "Proofs.lean").write_text(HEADER + "theorem Proofs.migrationCorrect : Generated.expected := 1\n")
    report = phase("prepare", *small.contract_arguments(), "--project", str(small.proofs),
                   "--output", str(tmp_path / "proof.bundle"))
    assert report["status"] == "UNVERIFIED" and "Proofs" in str(report["message"]), report
