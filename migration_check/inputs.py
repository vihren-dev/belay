"""Read the actual schema and migration SQL once per command and resolve them in Lean.

`verify`, `verify-bundle` and `prepare` all derive the generated Lean inputs the same
way, so a bundle is always checked against the SQL the verifier itself parsed. The
frontend maps the SQL to statement syntax; the trusted `migration-resolver` resolves
it and writes the generated modules. Python computes no resolution.
"""

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from belay.sqlite.located import Json, Located
from belay.sqlite.profiles import ExecutionProfile, profile
from belay.sqlite.sql_tree import parse
from belay.sqlite.syntax import script_record, statements
from .diagnostics import Rejection
from .process import run_process
from .runtime import Runtime


def read_sql(path: Path) -> bytes:
    """Bound input before allocation while preserving the exact bytes the parser checks."""
    with path.open("rb") as stream:
        sql = stream.read(1024 * 1024 + 1)
    if len(sql) > 1024 * 1024:
        raise Rejection("UNVERIFIED", "SQL exceeds the 1 MiB parser limit", source=str(path))
    return sql


@dataclass(frozen=True)
class GeneratedInputs:
    """Generated Lean sources and exact input identities for one request."""

    profile: ExecutionProfile
    schema_source: str
    sql_source: str
    schema_hash: str
    statements: int
    hashes: dict[str, str]
    structural: dict[str, Json]
    """The structural record that the resolver and both gates resolve."""
    runtime: Runtime
    """The installation that parsed the SQL; the command uses it for all later stages."""


def refusal(result: dict[str, Json], schema: tuple[Located, ...], script: tuple[Located, ...],
            options: argparse.Namespace) -> Rejection:
    """Turn the resolver's refusal into a diagnostic at the byte range of the refused node."""
    in_schema = result["status"] == "schemaError" or result.get("part") == "schema"
    located, source = (schema, options.schema) if in_schema else (script, options.migration)
    index = result["statement"]
    if type(index) is not int or not 0 <= index < len(located):
        raise Rejection("UNVERIFIED", "The resolver named a statement that does not exist; reinstall the verifier")
    path = result.get("path", [])
    start, end = located[index].span(path if isinstance(path, list) else [])
    if result["status"] == "schemaError":
        return Rejection("INPUT_ERROR", f"SQLite refuses this schema statement: {result['message']}; correct the "
                         "schema", source=str(source), start=start, end=end)
    return Rejection("UNSUPPORTED", str(result["reason"]), source=str(source), start=start, end=end)


def resolve(runtime: Runtime, record: dict[str, Json], schema: tuple[Located, ...],
            script: tuple[Located, ...], options: argparse.Namespace) -> tuple[str, str]:
    """Run the trusted resolver on the record; return the SchemaInputs and SqlInputs sources."""
    if not runtime.resolver.is_file():
        raise Rejection("INPUT_ERROR", f"Resolver is missing: {runtime.resolver}; run just build or reinstall")
    with TemporaryDirectory(prefix="migration-resolve-") as temporary:
        workspace = Path(temporary).resolve()
        record_path, output = workspace / "record.json", workspace / "generated"
        record_path.write_text(json.dumps(record), encoding="utf-8")
        output.mkdir()
        resolved = run_process([str(runtime.resolver), str(record_path), str(output)], write_root=workspace,
                               environment={}, timeout=30)
        if resolved.returncode != 0:
            raise Rejection("UNVERIFIED", resolved.stderr.strip() or "Resolver failed; reinstall the verifier")
        result = json.loads(resolved.stdout)
        if result["status"] != "resolved":
            raise refusal(result, schema, script, options)
        return ((output / "SchemaInputs.lean").read_text(encoding="utf-8"),
                (output / "SqlInputs.lean").read_text(encoding="utf-8"))


def generated_inputs(options: argparse.Namespace) -> GeneratedInputs:
    """Parse schema and migration with the pinned frontend and resolve them in Lean.

    The profile is checked before the runtime is located. The located runtime is
    part of the result, so a command checks the installation only once.
    """
    selected = profile(options.profile)
    runtime = Runtime.locate()
    parser = runtime.sql_parser(selected)
    schema_bytes, migration_bytes = read_sql(options.schema), read_sql(options.migration)
    schema = statements(parse(parser, schema_bytes, str(options.schema)))
    script = statements(parse(parser, migration_bytes, str(options.migration)))
    if not script:
        raise Rejection("INPUT_ERROR", "Migration must contain at least one statement", source=str(options.migration))
    record = script_record(selected, schema, script)
    schema_source, sql_source = resolve(runtime, record, schema, script, options)
    schema_hash = hashlib.sha256(schema_bytes).hexdigest()
    hashes = {"schema.sql": schema_hash, "migration.sql": hashlib.sha256(migration_bytes).hexdigest(),
              "profile": selected.engine}
    return GeneratedInputs(selected, schema_source, sql_source, schema_hash, len(script), hashes, record, runtime)
