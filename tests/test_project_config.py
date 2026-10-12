"""`migration_check.project_config`: the `belay.toml` reader that tests and experiments use for cases."""

from pathlib import Path

import pytest

from migration_check.project_config import ConfigError, discover, load

pytestmark = pytest.mark.unit

VALID = """\
[project]
profile = "3.51.0"
schema = "../approved/schema.sql"
migration = "migration.sql"
contract = "../approved"
baseline = "../approved/baseline.json"
proof_modules = ["NextInterpretation", "Proofs", "Helper"]

[test]
status = "VERIFIED"
"""
"""A case that shares its contract with other cases, as three checked-in examples do."""


def case_tree(root: Path, config: str = VALID) -> Path:
    """Write a case folder and a shared contract folder under `root`; return the config file."""
    (root / "approved").mkdir(parents=True)
    for name in ("Requirements.lean", "Interpretation.lean", "schema.sql", "baseline.json"):
        (root / "approved" / name).write_text("")
    case = root / "case"
    case.mkdir()
    for name in ("migration.sql", "NextInterpretation.lean", "Proofs.lean", "Helper.lean"):
        (case / name).write_text("")
    (case / "belay.toml").write_text(config)
    return case / "belay.toml"


def test_valid_config_resolves_shared_contract(tmp_path: Path) -> None:
    """Paths may leave the case folder while they stay inside the root; arguments name the resolved files."""
    config = load(case_tree(tmp_path), tmp_path)
    assert config.contract == (tmp_path / "approved").resolve()
    assert config.proof_modules == ("NextInterpretation", "Proofs", "Helper")
    assert config.test_status == "VERIFIED" and config.test_suite == "cli" and config.baseline is not None
    assert config.contract_arguments()[:2] == ["--profile", "3.51.0"]
    assert config.candidate_arguments()[-1] == str((tmp_path / "case" / "Proofs.lean").resolve())


@pytest.mark.parametrize("old,new,field", [
    ('profile = "3.51.0"\n', "", "project.profile"),
    ('profile = "3.51.0"', "profile = 3", "project.profile"),
    ('migration = "migration.sql"', 'migration = "missing.sql"', "project.migration"),
    ('contract = "../approved"', 'contract = "."', "project.contract"),
    ('"NextInterpretation", ', "", "project.proof_modules"),
    ('"Helper"', '"Absent"', "project.proof_modules"),
    ('status = "VERIFIED"', 'status = "PASSED"', "test.status"),
    ('status = "VERIFIED"', 'status = "VERIFIED"\nsuite = 1', "test.suite"),
    ('status = "VERIFIED"', 'status = ["VERIFIED"]', "test.status"),
    ('"Helper"', '"../../approved/Requirements"', "project.proof_modules"),
    ('"Helper"', '"/etc/passwd"', "project.proof_modules"),
    ('[test]', 'colour = "red"\n[test]', "project.colour"),
    ('[test]', '[extra]\n[test]', "(tables)"),
    ('[project]', '[project', "(file)"),
])
def test_wrong_field_names_file_and_field(tmp_path: Path, old: str, new: str, field: str) -> None:
    """Each missing, mistyped or unknown field is refused with the file and the field in the message."""
    file = case_tree(tmp_path, VALID.replace(old, new, 1))
    with pytest.raises(ConfigError, match=rf"belay\.toml: field {field.replace('(', '[(]').replace(')', '[)]')}:"):
        load(file, tmp_path)


def test_path_outside_root_is_refused(tmp_path: Path) -> None:
    """A path that leaves the folder holding the cases is refused, even when the file exists."""
    (tmp_path / "outside.sql").write_text("")
    root = tmp_path / "cases"
    file = case_tree(root, VALID.replace('migration = "migration.sql"', 'migration = "../../outside.sql"'))
    with pytest.raises(ConfigError, match="field project.migration: .* is outside"):
        load(file, root)


def test_discover_finds_nested_cases_in_order(tmp_path: Path) -> None:
    """Nested case folders, such as `application_keys/add_column_then_table`, are found."""
    for name in ("b/belay.toml", "a/nested/belay.toml", "a/belay.toml"):
        (tmp_path / name).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / name).write_text("")
    assert [p.relative_to(tmp_path).as_posix() for p in discover(tmp_path)] == [
        "a/belay.toml", "a/nested/belay.toml", "b/belay.toml"]


ROOT = Path(__file__).resolve().parents[1]
"""Repository checkout, whose `examples/` holds the checked-in cases."""


def test_every_checked_in_case_has_a_valid_config() -> None:
    """Each folder under `examples/` with a migration has a `belay.toml` that loads and names a status."""
    examples = ROOT / "examples"
    case_folders = sorted(path.parent for path in examples.rglob("migration.sql"))
    configs = {path.parent for path in discover(examples)}
    assert case_folders and set(case_folders) == configs, sorted(set(case_folders) ^ configs)
    for folder in case_folders:
        config = load(folder / "belay.toml", examples)
        assert config.test_status is not None, folder
