"""Discover the approved contract and compile the trusted stages for source `verify`.

Discovery (`discover_contract`, `source_hashes`) is shared by `verify`, `verify-bundle`
and `prepare`. `compile_trusted` compiles the generated schema, the approved contract
and the generated SQL for the deprecated `verify`, always freshly. `verify-bundle` and
`prepare` build with Lake and its artifact cache instead (ADR 0010, `contract_build`,
`project_phases`).
"""

from dataclasses import dataclass
import hashlib
from pathlib import Path

from .source_closure import Source, discover_sources, module_path

RESERVED_CONTRACT_STEM = "schemainputs"
"""Case-folded file stem that an approved source may not have: `SchemaInputs` is the generated starting schema."""

APPROVED_FORBIDDEN = frozenset({"NextInterpretation", "Generated", "Proofs", "SqlInputs", "SchemaInputs"})


@dataclass(frozen=True)
class Contract:
    """A snapshotted approved closure, its compile order and its imports from the trusted libraries."""

    sources: dict[str, Source]
    order: tuple[str, ...]
    external: frozenset[str]


def discover_contract(*, initial: dict[str, Source], roots: tuple[Path, ...], excluded: set[Path],
                      directory: Path, sysroot: Path, libraries: tuple[Path, Path], workspace: Path) -> Contract:
    """Snapshot the approved closure reachable from Requirements and Interpretation."""
    external: set[str] = set()
    sources, order = discover_sources(
        initial=initial, roots=roots, excluded=excluded, forbidden=set(APPROVED_FORBIDDEN),
        available={"SchemaInputs"}, directory=directory, sysroot=sysroot, libraries=libraries,
        workspace=workspace, external=external)
    return Contract(sources, order, frozenset(external))


def source_hashes(stage: str, sources: dict[str, Source]) -> dict[str, str]:
    """Report hashes in the public `stage/Module.lean` form used by baselines and artifacts."""
    return {f"{stage}/{module_path(name)}.lean": hashlib.sha256(source.contents).hexdigest()
            for name, source in sources.items()}


def compile_trusted(*, contract: Contract, approved_sources: Path, schema_inputs: str, sql_inputs: str | None,
                    trusted: Path, sysroot: Path, libraries: tuple[Path, Path], workspace: Path) -> list[str]:
    """Compile the schema, approved and SQL stages into `trusted`, every time.

    With `sql_inputs=None` the SQL stage is skipped: the bundle checker constructs those
    declarations itself from the frontend's structural record.
    """
    from .compile import compile_modules

    sql_sources = workspace / "sql-sources"
    schema_output, sql_output = workspace / "schema-output", workspace / "sql-output"
    for directory in (sql_sources, schema_output, sql_output):
        directory.mkdir()
    # Starting schema has no access to approved or candidate sources/artifacts.
    (sql_sources / "SchemaInputs.lean").write_text(schema_inputs, encoding="utf-8")
    common = {"sysroot": sysroot, "libraries": libraries, "workspace": workspace}
    diagnostics = compile_modules(order=("SchemaInputs",), sources=sql_sources, destination=schema_output,
                                  previous=(), **common)
    diagnostics += compile_modules(order=contract.order, sources=approved_sources, destination=trusted,
                                   previous=(schema_output,), **common)
    if sql_inputs is not None:
        (sql_sources / "SqlInputs.lean").write_text(sql_inputs, encoding="utf-8")
        diagnostics += compile_modules(order=("SqlInputs",), sources=sql_sources, destination=sql_output,
                                       previous=(schema_output,), **common)
    for directory in (schema_output, sql_output):
        for artifact in directory.rglob("*"):
            if artifact.is_file():
                target = trusted / artifact.relative_to(directory)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(artifact.read_bytes())
                target.chmod(0o444)
    return diagnostics


@dataclass(frozen=True)
class CompiledContract:
    """Trusted stage outputs for the bundle path, with input hashes and trusted imports."""

    trusted: Path
    hashes: dict[str, str]
    external: frozenset[str]
    modules: frozenset[str]
