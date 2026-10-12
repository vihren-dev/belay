"""Discover a proofs project's modules and check its lakefile (ADR 0010 sections 1 and 2).

Discovery applies the source rules of `verify` to the approved contract and to the
candidate modules, and finds the trusted imports that the bundle names. The lakefile
checks catch, before Lake runs, a project that would build another contract or that
does not list a module Lake must build.
"""

from dataclasses import dataclass
from pathlib import Path

from .compile import EXPECTED_SOURCE
from .contract import Contract, discover_contract
from .diagnostics import Rejection
from .proofs_project import (AUDIT_MODULE, GENERATED_MODULES, check_disabling_settings, missing_modules,
                             reads_contract_from)
from .runtime import Runtime
from .source_closure import Source, discover_sources, role_sources

CANDIDATE_ROOTS = ("NextInterpretation", "Proofs")
"""Candidate modules that every proofs project has, at its top level."""


@dataclass(frozen=True)
class Discovery:
    """The approved closure, the candidate modules (without `Generated`) and the trusted imports."""

    contract: Contract
    candidates: tuple[str, ...]
    trusted_imports: frozenset[str]


def discover_project(*, runtime: Runtime, requirements: Path, interpretation: Path, project: Path,
                     workspace: Path) -> Discovery:
    """Apply today's source rules to the contract and the candidate modules, in snapshots under `workspace`.

    Candidate modules may import the contract and the generated inputs but not provide
    their own `SchemaInputs` or `SqlInputs`.
    """
    selected = {"Requirements": requirements.resolve(strict=True), "Interpretation": interpretation.resolve(strict=True)}
    contract = discover_contract(
        initial=role_sources(selected), roots=tuple(dict.fromkeys(path.parent for path in selected.values())),
        excluded=set(), directory=workspace / "approved", sysroot=runtime.sysroot, libraries=runtime.libraries,
        workspace=workspace)
    external: set[str] = set(contract.external)
    initial = {name: Source(path, path.read_bytes()) for name in CANDIDATE_ROOTS
               for path in [(project / f"{name}.lean").resolve(strict=True)]}
    initial["Generated"] = Source(None, EXPECTED_SOURCE.encode())
    _, order = discover_sources(
        initial=initial, roots=(project,), excluded=set(), forbidden={"SchemaInputs", "SqlInputs"},
        available=set(contract.sources) | {"SchemaInputs", "SqlInputs"}, directory=workspace / "candidate",
        sysroot=runtime.sysroot, libraries=runtime.libraries, workspace=workspace, external=external)
    return Discovery(contract, tuple(name for name in order if name != "Generated"), frozenset(external))


def check_lakefile(project: Path, requirements: Path, discovery: Discovery) -> None:
    """Refuse a TOML lakefile that reads another contract or does not list a module; a `lakefile.lean`, which
    is code, is not read."""
    lakefile = project / "lakefile.toml"
    if not lakefile.is_file():
        return
    text = lakefile.read_text(encoding="utf-8")
    approved = requirements.resolve().parent
    if not reads_contract_from(text, project, approved):
        raise Rejection("INPUT_ERROR", f"{lakefile} has no library that reads Requirements and Interpretation "
                        f"from {approved}; set that library's srcDir to the approved folder")
    missing = missing_modules(text, [*discovery.contract.order, *GENERATED_MODULES, AUDIT_MODULE,
                                     *discovery.candidates])
    if missing:
        raise Rejection("INPUT_ERROR", f"{lakefile} lists no library for the modules {', '.join(missing)}; "
                        "add each one to the roots of the library whose folder holds it")
    disabling = check_disabling_settings(text)
    if disabling:
        raise Rejection("INPUT_ERROR", f"{lakefile} turns off kernel checking ({'; '.join(disabling)}); "
                        "remove these settings, which the verifier would not apply either")
