"""Select compiled library modules and retain their source and artifact identities."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import TypedDict, cast


class Module(TypedDict):
    """An explicitly selected module, independent of any umbrella import closure."""

    name: str
    source: str
    package: str


PACKAGES = {
    "belay-sqlite-model": "Belay",
    "belay-sqlite-text": "Belay",
    "belay": "Belay",
    "verifier-conformance": "VerifierConformance",
}
"""The source trees of the default libraries, including separately compiled example modules."""

EXCLUSIONS = [
    "Build tools and executable entry points outside the selected library trees.",
    "Tests and experiments outside those trees, unless selected by an explicit manifest.",
    "Third-party declarations are boundary nodes; their bodies are outside the selected scope.",
    "Discarded tactic searches and anonymous proofs that do not survive compilation.",
]


def object_value(value: object, context: str) -> dict[str, object]:
    """Reject malformed JSON objects at the boundary with their input context."""
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise ValueError(f"{context}: expected an object")
    return cast(dict[str, object], value)


def object_list(value: object, context: str) -> list[dict[str, object]]:
    """Read a JSON array of records without accepting strings as sequences."""
    if not isinstance(value, list):
        raise ValueError(f"{context}: expected an array")
    return [object_value(item, context) for item in value]


def digest(path: Path) -> str:
    """Identify the exact bytes of a selected source or compiled artifact."""
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def default_modules(root: Path) -> list[Module]:
    """Select every library source, including sources omitted from umbrella imports."""
    modules: list[Module] = []
    for package, tree in PACKAGES.items():
        folder = root / "packages" / package
        if not (folder / tree).is_dir():
            raise ValueError(f"{folder / tree}: library source tree is missing; select built packages")
        sources = list((folder / tree).rglob("*.lean"))
        umbrella = folder / f"{tree}.lean"
        if umbrella.is_file():
            sources.append(umbrella)
        modules.extend(Module(name=".".join(source.relative_to(folder).with_suffix("").parts),
                              source=str(source.resolve()), package=package) for source in sources)
    if len({module["name"] for module in modules}) != len(modules):
        raise ValueError("Default library trees contain repeated module names; select one owning package per module")
    return sorted(modules, key=lambda module: module["name"])


def read_manifest(path: Path) -> list[Module]:
    """Resolve manifest source paths relative to the manifest and reject ambiguous selections."""
    document = object_value(json.loads(path.read_text()), str(path))
    modules: list[Module] = []
    for row in object_list(document.get("modules"), f"{path}: modules"):
        for field in ("name", "source", "package"):
            if not isinstance(row.get(field), str) or not row[field]:
                raise ValueError(f"{path}: module {field} must be a nonempty string")
        name, source, package = (cast(str, row[key]) for key in ("name", "source", "package"))
        if any(part in ("", "..") or "/" in part or "\\" in part for part in name.split(".")):
            raise ValueError(f"{path}: invalid module name {name!r}")
        modules.append(Module(name=name, source=str((path.parent / source).resolve()), package=package))
    names = [module["name"] for module in modules]
    if not names or len(set(names)) != len(names):
        raise ValueError(f"{path}: select at least one module and give each module name once")
    return sorted(modules, key=lambda module: module["name"])


def merge_libraries(paths: list[Path], destination: Path) -> None:
    """Merge compiled roots because Lean otherwise shadows packages sharing the Belay namespace."""
    destination.mkdir(parents=True)
    for root in paths:
        if not root.is_dir():
            raise ValueError(f"{root}: compiled library directory is missing; rebuild the selected package")
        for source in sorted(root.rglob("*")):
            if not source.is_file() or not (source.name.endswith((".olean", ".ilean", ".ir"))
                                            or ".olean." in source.name):
                continue
            target = destination / source.relative_to(root)
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                if target.resolve() != source.resolve() and digest(target) != digest(source):
                    raise ValueError(f"{source}: conflicts with {target.resolve()}; select one compiled version")
            else:
                target.symlink_to(source.resolve())


def selected_artifacts(modules: list[Module], library: Path) -> dict[str, dict[str, object]]:
    """Fail before extraction if any selected source or artifact is absent, and identify each pair."""
    artifacts: dict[str, dict[str, object]] = {}
    missing: list[str] = []
    for module in modules:
        source = Path(module["source"])
        artifact = library.joinpath(*module["name"].split(".")).with_suffix(".olean")
        if not source.is_file():
            missing.append(f"{module['name']}: missing source {source}")
        if not artifact.is_file():
            missing.append(f"{module['name']}: missing compiled artifact {artifact.name}")
        if source.is_file() and artifact.is_file():
            files = [artifact] + [path for suffix in ("private", "server")
                                  if (path := artifact.with_name(f"{artifact.name}.{suffix}")).is_file()]
            artifacts[module["name"]] = {"sourceSha256": digest(source),
                "artifact": str(artifact.resolve()), "artifactSha256": digest(artifact),
                "artifactFiles": [{"path": str(path.resolve()), "sha256": digest(path)} for path in files]}
    if missing:
        raise ValueError("Selected module coverage is incomplete; compile these modules or correct the manifest:\n"
                         + "\n".join(missing))
    return artifacts
