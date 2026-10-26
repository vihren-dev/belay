"""Check narrow imports by compiling unchanged bodies from three surface modules.

The copies are disposable experiment inputs. Source-derived project import closures
measure dependency scope, not compilation time or proof necessity.
"""

import json
from pathlib import Path
import re
import subprocess


NARROW_IMPORTS = {
    "Values": ["Comparison", "Declarations", "StoreValue", "StoreValueLaws", "Truth"],
    "Script": ["Declarations", "Resolution.Syntax", "SqlAdvance"],
    "ValueDisplay": ["Declarations", "OutputRepr"],
}
"""Owners of the used model declarations, including Values' source-level exports."""


def project_sources(packages: tuple[Path, ...]) -> dict[str, str]:
    """Read packaged project modules, excluding generated Lake build directories."""
    sources: dict[str, str] = {}
    for package in packages:
        for path in (package / "Belay").rglob("*.lean"):
            name = ".".join(path.relative_to(package).with_suffix("").parts)
            if name in sources:
                raise RuntimeError(f"Duplicate project module {name}")
            sources[name] = path.read_text()
        root = package / "Belay.lean"
        if root.exists():
            sources["Belay"] = root.read_text()
    return sources


def imports(source: str) -> list[str]:
    """Read explicit imports in the selected modules' existing source syntax."""
    return re.findall(r"^import ([\w.]+)$", source, re.MULTILINE)


def closure(roots: list[str], sources: dict[str, str]) -> list[str]:
    """Return the transitive selected-project imports, counting each module once."""
    reached: set[str] = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name in reached or name not in sources:
            continue
        reached.add(name)
        pending.extend(imports(sources[name]))
    return sorted(reached)


def check_imports(output: Path, model: Path, surface: Path, text: Path) -> None:
    """Compile each baseline and narrowed copy; record closures and exact sources."""
    sources = project_sources((model, surface, text))
    reports = {}
    for name, owners in NARROW_IMPORTS.items():
        original = sources[f"Belay.Sqlite.{name}"]
        if original.count("import Belay.Sqlite.Model\n") != 1:
            raise RuntimeError(f"{name}: expected exactly one model umbrella import")
        narrow = original.replace("import Belay.Sqlite.Model\n", "".join(
            f"import Belay.Sqlite.Model.{owner}\n" for owner in owners
        ))
        variants = {"baseline": original, "narrow": narrow}
        for variant, source in variants.items():
            path = Path(f"Imports{name}{variant.title()}.lean")
            path.write_text(source)
            result = subprocess.run(
                ["lean", "-o", str(path.with_suffix(".olean")), str(path)],
                capture_output=True, text=True, timeout=120, check=False,
            )
            log = result.stdout + result.stderr
            (output / f"{path.stem}.log").write_text(log)
            (output / path.name).write_text(source)
            if result.returncode or re.search(r"\b(?:warning|error)(?:\([^)]*\))?:", log):
                raise RuntimeError(f"{path.name} failed.\n{log}")
        reports[name] = {
            variant: {"imports": imports(source), "closure": closure(imports(source), sources)}
            for variant, source in variants.items()
        }
        print(f"{name}: baseline and narrow source bodies compile", flush=True)
    (output / "imports.json").write_text(json.dumps(reports, indent=2) + "\n")
