"""Compile the approved contract and the starting schema with Lake (ADR 0010 sections 1 and 5).

`verify-bundle` builds only trusted inputs: the snapshotted approved closure and
the generated `SchemaInputs`. Discovery, role rules and the baseline check are
the same as before (`contract.discover_contract`); Lake replaces the per-module
compiles and reuses outputs from the caller's cache, which belongs to the
verifier's trust domain.
"""

import argparse
from collections.abc import Iterator
from contextlib import contextmanager
import hashlib
import os
from pathlib import Path
import sys
from tempfile import TemporaryDirectory

from .baseline import check_baseline
from .cache_location import cache_directory, runtime_version
from .contract import RESERVED_CONTRACT_STEM, CompiledContract, discover_contract, source_hashes
from .lake_workspace import Library, lake_build, write_workspace
from .runtime import Runtime, validate_libraries
from .source_closure import role_sources

LIBRARY_PREFIXES = ("SqliteVerifier", "Belay", "GateCore", "GatePaths")
"""Module prefixes of the installed packages; Lake replays them and never compiles them here."""


@contextmanager
def selected_cache(options: argparse.Namespace, runtime: Runtime) -> Iterator[Path]:
    """The cache of this run: `--no-cache` gives a private empty folder, else `--cache`, `BELAY_CACHE_DIR` or
    the per-user default."""
    if options.no_cache:
        with TemporaryDirectory(prefix="belay-no-cache-") as temporary:
            yield Path(temporary)
        return
    folder = cache_directory(options.cache, os.environ, Path.home(), sys.platform,
                             runtime_version(runtime.sysroot, runtime.libraries))
    folder.mkdir(parents=True, exist_ok=True)
    yield folder


def build_contract(*, runtime: Runtime, requirements: Path, interpretation: Path, schema_inputs: str,
                   sql_inputs: str, workspace: Path, cache: Path, approved_baseline: Path | None,
                   schema_hash: str) -> tuple[CompiledContract, tuple[str, ...]]:
    """Check optional approval, then build the approved closure and `SchemaInputs` in a Lake workspace.

    Returns the trusted outputs and the modules that Lake compiled (none when the
    cache had them). `SqlInputs` is not compiled: the bundle checker constructs those
    declarations itself. Its source hash is still reported.
    """
    validate_libraries(runtime.sysroot, runtime.libraries)
    selected = {"Requirements": requirements.resolve(strict=True),
                "Interpretation": interpretation.resolve(strict=True)}
    if any(path.stem.casefold() == RESERVED_CONTRACT_STEM for path in selected.values()):
        raise ValueError("SchemaInputs is reserved for generated starting schema")
    approved, generated = workspace / "approved", workspace / "generated"
    for directory in (approved, generated):
        directory.mkdir(parents=True)
    contract = discover_contract(
        initial=role_sources(selected), roots=tuple(dict.fromkeys(path.parent for path in selected.values())),
        excluded=set(), directory=approved, sysroot=runtime.sysroot, libraries=runtime.libraries,
        workspace=workspace)
    hashes = source_hashes("approved", contract.sources)
    hashes["generated/SchemaInputs.lean"] = hashlib.sha256(schema_inputs.encode()).hexdigest()
    hashes["generated/SqlInputs.lean"] = hashlib.sha256(sql_inputs.encode()).hexdigest()
    if approved_baseline is not None:
        check_baseline(approved_baseline, {**hashes, "schema.sql": schema_hash})
    (generated / "SchemaInputs.lean").write_text(schema_inputs, encoding="utf-8")
    write_workspace(workspace, "verification", runtime.root, [
        Library("Contract", "approved", contract.order), Library("GeneratedInputs", "generated", ("SchemaInputs",))])
    compiled = lake_build(workspace, runtime.sysroot, cache, LIBRARY_PREFIXES)
    return (CompiledContract(workspace / ".lake/build/lib/lean", hashes, contract.external,
                             frozenset(contract.sources)), compiled)
