"""ADR 0003 data path through the public entrypoint: `prepare` then `verify-bundle`."""

from collections.abc import Callable
import hashlib
import json
import shutil
from pathlib import Path

import pytest

from migration_check.project_config import ProjectConfig, load
from tests.runtime_support import CommandResult
from tests.example_cases import input_digests
from tests.proof_exporter_test import exporter_runtime_identity

pytestmark = [pytest.mark.e2e, pytest.mark.kernel, pytest.mark.requires_lean, pytest.mark.requires_native]
APPLICATION_KEY_HEADER = {"bundle": 1, "trusted_imports": ["Init", "SqliteVerifier.ApplicationKeyDemonstration"]}
"""The authored variant imports the complete application-key certificate from the selected library."""


TOOL_AND_LAKE_FILES = (".lake", ".belay", "Generated", "lakefile.toml", "lake-manifest.json", "lean-toolchain")
"""Files of a proofs project that `init`, `prepare` and Lake write; a copied candidate starts without them."""


@pytest.fixture
def data_path(runtime_root: Path, tmp_path: Path,
              command_runner: Callable[..., CommandResult]) -> Callable[..., dict[str, object]]:
    """Prepare a bundle from one contract/candidate pair, then verify it against another contract."""
    def run(*, approved: Path, candidate: Path, schema: Path, profile: str = "3.51.0",
            checked_approved: Path | None = None, checked_migration: Path | None = None,
            directory: Path | None = None, audit: bool = True, cache: Path | None = None) -> dict[str, object]:
        """Return verify-bundle's JSON report after asserting prepare succeeded."""
        def common(contract: Path, migration: Path) -> list[str]:
            return ["--profile", profile, "--format", "json", "--schema", str(schema),
                    "--requirements", str(contract / "Requirements.lean"),
                    "--interpretation", str(contract / "Interpretation.lean"), "--migration", str(migration)]
        selected = directory or tmp_path
        selected.mkdir(exist_ok=True)
        bundle = selected / "proof.bundle"
        launcher = str(runtime_root / "bin/migration-check")
        # A fresh proofs project for exactly this contract: the candidate's files and a lakefile from `init`.
        project = selected / "project"
        shutil.copytree(candidate, project, ignore=shutil.ignore_patterns(*TOOL_AND_LAKE_FILES))
        created = command_runner([launcher, "init", "--format", "json", "--project", str(project),
                                  "--requirements", str(approved / "Requirements.lean"),
                                  "--interpretation", str(approved / "Interpretation.lean")], cwd=tmp_path, timeout=120)
        assert created.returncode == 0, created.diagnostic()
        caching = ["--cache", str(cache)] if cache is not None else []
        inputs, target = [*common(approved, candidate / "migration.sql"), "--project", str(project)], str(bundle)
        # Without the audit, the phases build a bundle as an agent's own tools could; verify-bundle judges it.
        steps = ([["prepare", *inputs, "--output", target, *caching]] if audit else
                 [["generate", *inputs], ["check", "--project", str(project), "--format", "json", *caching],
                  ["export", *inputs, "--output", target, *caching]])
        for step in steps:
            prepared = command_runner([launcher, *step], cwd=tmp_path, timeout=180)
            assert prepared.returncode == 0, prepared.diagnostic()
        checked = command_runner([launcher, "verify-bundle",
                                  *common(checked_approved or approved, checked_migration or candidate / "migration.sql"),
                                  "--bundle", str(bundle), *caching], cwd=tmp_path, timeout=120)
        report = checked.json_object()
        assert checked.returncode == (0 if report["status"] == "VERIFIED" else 1), checked.diagnostic()
        return report
    return run


def case_options(config: ProjectConfig) -> dict[str, object]:
    """`data_path` arguments for a case, from its `belay.toml`."""
    return {"approved": config.contract, "candidate": config.proofs, "schema": config.schema,
            "profile": config.profile}


def test_allowed_failure_through_data_path(data_path: Callable[..., dict[str, object]],
                                          example_factory: Callable[[str], Path]) -> None:
    """The allowed-failure example is VERIFIED through `prepare` and `verify-bundle`.

    The other shipped examples go through the data path in `test_current_native_export` and
    `test_application_key_bundle_repeatability`, which also check their status.
    """
    examples = example_factory("allowed_failure")
    config = load(examples / "belay.toml", examples)
    report = data_path(**case_options(config))
    assert report["status"] == config.test_status, report


def test_application_key_bundle_repeatability(data_path: Callable[..., dict[str, object]],
        example_factory: Callable[[str], Path], tmp_path: Path, runtime_root: Path,
        exporter_runtime_identity: dict[str, object], record_testsuite_property: Callable[[str, object], None]) -> None:
    """Independent preparation binds identical keyed certificates to the selected inputs and library."""
    examples = example_factory("application_keys")
    config = load(examples / "add_column_then_table/belay.toml", examples)
    options = case_options(config)
    hashes = input_digests(examples, "approved", "add_column_then_table", "approved/schema.sql")
    assert hashes == input_digests(runtime_root / "examples/application_keys", "approved",
                                  "add_column_then_table", "approved/schema.sql")
    reports = [data_path(**options, directory=tmp_path / label) for label in ("first", "second")]
    payloads = [(tmp_path / label / "proof.bundle").read_bytes() for label in ("first", "second")]
    for report, payload in zip(reports, payloads, strict=True):
        assert report["status"] == config.test_status and json.loads(payload.splitlines()[0]) == APPLICATION_KEY_HEADER
        expected = {"profile": "3.51.0", "schema.sql": hashes["approved/schema.sql"],
            "migration.sql": hashes["add_column_then_table/migration.sql"], "bundle": hashlib.sha256(payload).hexdigest(),
            **{name: digest for name, digest in hashes.items() if name.startswith("approved/") and name.endswith(".lean")}}
        assert isinstance(report["inputs"], dict) and expected.items() <= report["inputs"].items(), report
    assert payloads[0] == payloads[1]
    record_testsuite_property("application-key-example", json.dumps({"inputSha256": hashes,
        "runtime": exporter_runtime_identity, "header": APPLICATION_KEY_HEADER,
        "bundleSha256": hashlib.sha256(payloads[0]).hexdigest(), "checks": reports}, sort_keys=True))


@pytest.fixture
def small(example_factory: Callable[[str], Path]) -> dict[str, Path]:
    """Private copies of the small approved contract and positive candidate, as their `belay.toml` names them."""
    examples = example_factory(".")
    config = load(examples / "add_column_then_table/belay.toml", examples)
    reverse = load(examples / "table_then_column/belay.toml", examples)
    return {"approved": config.contract, "candidate": config.proofs, "schema": config.schema,
            "reverse": reverse.proofs}


@pytest.mark.parametrize("proof,diagnostic", [
    ("theorem Proofs.migrationCorrect : Generated.expected := by sorry", "sorryAx"),
    ("axiom unapproved : Generated.expected\ntheorem Proofs.migrationCorrect : Generated.expected := unapproved",
     "unapproved axiom"),
    ("theorem Proofs.migrationCorrect : True := trivial", "reconstructed verification target"),
], ids=["sorry", "forbidden_axiom", "wrong_target"])
def test_invalid_proof_rejected(data_path: Callable[..., dict[str, object]], small: dict[str, Path],
                                proof: str, diagnostic: str) -> None:
    """Unfinished proofs, extra axioms and proofs of another statement are UNVERIFIED in `verify-bundle`, also
    for a bundle exported without the audit that `prepare` runs."""
    (small["candidate"] / "Proofs.lean").write_text("import Generated\n" + proof + "\n")
    report = data_path(approved=small["approved"], candidate=small["candidate"], schema=small["schema"],
                       audit=False)
    assert report["status"] == "UNVERIFIED" and diagnostic in str(report["message"]), report


def test_bundle_from_altered_contract_rejected(data_path: Callable[..., dict[str, object]],
                                                small: dict[str, Path], tmp_path: Path) -> None:
    """A bundle built against an altered copy of the contract cannot replace the approved one."""
    altered = tmp_path / "altered"
    altered.mkdir()
    for name in ("Requirements.lean", "Interpretation.lean"):
        (altered / name).write_bytes((small["approved"] / name).read_bytes())
    requirements = altered / "Requirements.lean"
    # Definitionally equal, so the candidate still compiles, but a different declaration record.
    changed = requirements.read_text().replace("valid := fun _ => True",
                                               "valid := fun _ => (fun (claim : Prop) => claim) True")
    assert changed != requirements.read_text()
    requirements.write_text(changed)
    report = data_path(approved=altered, candidate=small["candidate"], schema=small["schema"],
                       checked_approved=small["approved"])
    assert report["status"] == "UNVERIFIED" and "modified protected declaration" in str(report["message"]), report


def test_bundle_bound_to_prepared_sql(data_path: Callable[..., dict[str, object]], small: dict[str, Path]) -> None:
    """A bundle prepared for one migration cannot verify a different migration's SQL."""
    report = data_path(approved=small["approved"], candidate=small["candidate"], schema=small["schema"],
                       checked_migration=small["reverse"] / "migration.sql")
    assert report["status"] == "UNVERIFIED" and "modified protected declaration" in str(report["message"]), report


def test_shared_interpretation_file(data_path: Callable[..., dict[str, object]], small: dict[str, Path],
                                    tmp_path: Path) -> None:
    """One file may supply both the current and next interpretation: the proofs project's
    `NextInterpretation` imports the approved `Interpretation`, which defines both."""
    shared = tmp_path / "shared"
    shared.mkdir()
    (shared / "Requirements.lean").write_bytes((small["approved"] / "Requirements.lean").read_bytes())
    current = (small["approved"] / "Interpretation.lean").read_text().replace(
        "import Requirements\n", "import Requirements\nimport SqliteVerifier.Demonstration\n")
    (shared / "Interpretation.lean").write_text(current + """
namespace NextInterpretation
def next : SqliteVerifier.Interpretation Requirements.LogicalState := SqliteVerifier.Demonstration.next Generated.profile
def failures : SqliteVerifier.FailureRepresentation Requirements.LogicalState := SqliteVerifier.unreachableFailures
end NextInterpretation
""")
    candidate = tmp_path / "candidate"
    candidate.mkdir()
    (candidate / "migration.sql").write_bytes((small["candidate"] / "migration.sql").read_bytes())
    (candidate / "Proofs.lean").write_bytes((small["candidate"] / "Proofs.lean").read_bytes())
    (candidate / "NextInterpretation.lean").write_text("import Interpretation\n")
    report = data_path(approved=shared, candidate=candidate, schema=small["schema"])
    assert report["status"] == "VERIFIED", report

