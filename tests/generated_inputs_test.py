"""ADR 0003 P3: declarations the bundle checker constructs agree with today's Lean emitter."""

from collections.abc import Callable
import json
import os
from pathlib import Path

import pytest

from migration_check.contract import Contract, compile_trusted
from belay.sqlite.profiles import profile
from migration_check.lean_inputs import schema_inputs, sql_inputs
from migration_check.project_config import load as load_config
from belay.sqlite.sql_tree import Tree
from belay.sqlite.structural import Json, generated_inputs_wire
from belay.sqlite.translate import starting_schema, statements
from tests.runtime_support import CommandResult, run_command
from tests.sql_fixtures import RICH_BASELINE

pytestmark = [pytest.mark.integration, pytest.mark.kernel, pytest.mark.requires_lean, pytest.mark.requires_native]
ROOT = Path(__file__).resolve().parents[1]
LEDGER = "CREATE TABLE ledger(version BIGINT PRIMARY KEY, label TEXT, stamp TIMESTAMP, ok BOOLEAN, data BLOB);"
WRITES = ("BEGIN; INSERT INTO ledger(version,label,stamp,ok,data) "
          "VALUES(-9223372036854775808,'can''t λ \\ \"q\"','2026-09-25 00:00:00',NULL,X'00ff7f80'); COMMIT; "
          "INSERT INTO ledger(version,label,stamp,ok,data) VALUES(9223372036854775807,'',NULL,1,X''); "
          "UPDATE ledger SET ok=-1 WHERE version=7; BEGIN; UPDATE ledger SET label=NULL WHERE version=0; ROLLBACK;")


Source = Callable[[Path], tuple[str, str, str]]
"""Schema SQL, migration SQL and SQLite profile of one case, given the runtime under test."""


def example(name: str) -> Source:
    """A case shipped in the selected runtime, with the inputs its `belay.toml` names."""
    def read(runtime: Path) -> tuple[str, str, str]:
        """Load the case's configuration from the runtime's own examples."""
        examples = runtime / "examples"
        config = load_config(examples / name / "belay.toml", examples)
        return config.schema.read_text(), config.migration.read_text(), config.profile
    return read


def conformance_case(name: str, version: str) -> Source:
    """Schema and migration SQL of an ADR 0004 authored case, under the given profile."""
    def load(_runtime: Path) -> tuple[str, str, str]:
        """Read the checked-in structural case; only its SQL is used here."""
        case = json.loads((ROOT / "conformance/cases" / f"{name}.json").read_text())
        return case["schemaSql"], case["migrationSql"], version
    return load


def literal(schema_sql: str, migration_sql: str, version: str) -> Source:
    """A hand-written schema and migration, under the given profile."""
    return lambda _runtime: (schema_sql, migration_sql, version)


CASES: dict[str, Source] = {
    "add_column_then_table": example("add_column_then_table"),
    "table_then_column": example("table_then_column"),
    "refutation_unchanged_invoices": example("missing_required_column"),
    "allowed_failure": example("allowed_failure"),
    "atuin_3_46": example("atuin"),
    "literal_writes_and_transactions": literal(LEDGER, WRITES, "3.46.0"),
    "rich_schema_nullable_add": literal(RICH_BASELINE, "ALTER TABLE events ADD extra TEXT;", "3.51.0"),
    "unchanged_schema": literal(LEDGER, "BEGIN; COMMIT;", "3.51.0"),
    "unicode_names": literal('CREATE TABLE "Café"("Имя" TEXT, n INTEGER);',
                             'ALTER TABLE "Café" ADD "💡" BLOB; CREATE TABLE extra(r REAL, n NUMERIC);', "3.51.0"),
    **{f"conformance_{name}": conformance_case(name, "3.51.0")
       for name in ("add_then_create", "missing_table_prefix", "retained_add_prefix", "retained_create_prefix")},
}


@pytest.fixture
def parity(runtime_root: Path, lean_sysroot: Path, lean_libraries: tuple[Path, Path], tmp_path: Path,
           parse_sql: Callable[..., Tree]) -> Callable[..., CommandResult]:
    """Compile today's SchemaInputs/SqlInputs, then ask the checker to compare its construction."""
    def check(schema_sql: str, migration_sql: str, version: str,
              mutate: Callable[[dict[str, Json]], object] | None = None) -> CommandResult:
        """Return the checker's `--parity` result, optionally for a tampered record."""
        schema = starting_schema(parse_sql(schema_sql, version))
        script = statements(parse_sql(migration_sql, version))
        selected = profile(version)
        workspace, trusted, approved = tmp_path / "work", tmp_path / "trusted", tmp_path / "approved"
        for directory in (workspace, trusted, approved):
            directory.mkdir()
        compile_trusted(contract=Contract({}, (), frozenset()), approved_sources=approved,
                        schema_inputs=schema_inputs(schema), sql_inputs=sql_inputs(schema, script, selected),
                        trusted=trusted, sysroot=lean_sysroot, libraries=tuple(path.resolve() for path in lean_libraries),
                        workspace=workspace)
        record = generated_inputs_wire(schema, script, selected)
        if mutate is not None:
            mutate(record)
        generated = tmp_path / "generated.json"
        generated.write_text(json.dumps(record))
        return run_command([str(runtime_root / ".lake/build/bin/migration-bundle-checker"), "--parity",
                            *[str(path.resolve()) for path in lean_libraries], str(trusted), str(generated)], cwd=tmp_path, timeout=60,
                           environment={**os.environ, "LEAN_SYSROOT": str(lean_sysroot)})
    return check


@pytest.mark.parametrize("name", CASES)
def test_constructed_declarations_match_emitter(parity: Callable[..., CommandResult], runtime_root: Path,
                                                name: str) -> None:
    """nextSchema, script and profile have the emitter's types and definitionally equal values."""
    schema_sql, migration_sql, version = CASES[name](runtime_root)
    result = parity(schema_sql, migration_sql, version)
    assert result.returncode == 0, result.diagnostic()


@pytest.mark.parametrize("change,diagnostic", [
    (lambda record: record["schema"][0].update(name="other"), "do not match the compiled starting schema"),
    (lambda record: record.update(version=2), "only version 1 is supported"),
    (lambda record: record.pop("script"), "bundle checker rejected"),
    (lambda record: record["script"].append("commit"), "value differs from the emitter: Generated.script"),
    (lambda record: record.update(profile="sqlite346"), "value differs from the emitter: Generated.profile"),
], ids=["changed_start_schema", "other_version", "missing_field", "extra_statement", "other_profile"])
def test_tampered_record_is_rejected(parity: Callable[..., CommandResult], runtime_root: Path,
                                     change: Callable[[dict[str, Json]], object], diagnostic: str) -> None:
    """A record that disagrees with the compiled inputs, or is malformed, is rejected."""
    schema_sql, migration_sql, _version = example("add_column_then_table")(runtime_root)
    result = parity(schema_sql, migration_sql, "3.51.0", change)
    assert result.returncode == 1 and diagnostic in result.stderr, result.diagnostic()
