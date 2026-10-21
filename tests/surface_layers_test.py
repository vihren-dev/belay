"""The layer rules of the surface (ADR 0016, D2), read from the import lines of every Lean
package and from the Nix build.

1. Nothing below the surface imports it: no Lean file of another package under `packages/`
   imports a module of `packages/belay`, and no other lakefile requires it.
2. The surface imports the model only through its roots `Belay.Sqlite.Model` and
   `Belay.Sqlite.Model.Codec`, and otherwise only `Init`, `Std`, `Lean` and its own modules.
3. The conformance runtime does not contain the surface: in `build-support/`, only the
   surface's own derivation and the `surface` test suite name it.
"""

from pathlib import Path
import re

import pytest

pytestmark = pytest.mark.unit

ROOT = Path(__file__).resolve().parents[1]
PACKAGES = ROOT / "packages"
SURFACE = PACKAGES / "belay"
MODEL_ROOTS = {"Belay.Sqlite.Model", "Belay.Sqlite.Model.Codec"}
"""The model's root modules, the only model modules that the surface may import."""
EXTERNAL_ROOTS = {"Init", "Std", "Lean"}
"""The Lean libraries that the surface may import."""
SURFACE_NAMES = re.compile(r"surfacePackage|sources\.surface|packages/belay\b(?!-)")
"""The ways that a Nix file names the surface package."""


def lean_files(package: Path) -> list[Path]:
    """The Lean files of a package, without Lake's build folder."""
    return [path for path in package.rglob("*.lean") if ".lake" not in path.relative_to(package).parts]


def module_name(package: Path, path: Path) -> str:
    """The module that a Lean file of a package defines."""
    return ".".join(path.relative_to(package).with_suffix("").parts)


def imports(path: Path) -> list[str]:
    """The modules that a Lean file imports, from its `import` lines."""
    return [name for line in re.findall(r"(?m)^import (.+)$", path.read_text()) for name in line.split()]


def surface_modules() -> set[str]:
    """The modules of the surface package, without its lakefile."""
    return {module_name(SURFACE, path) for path in lean_files(SURFACE) if path.name != "lakefile.lean"}


def test_the_surface_package_has_modules() -> None:
    """The rules below read the surface's files; an empty set would make them pass vacuously."""
    assert {"Belay", "Belay.Sqlite"} <= surface_modules()


def test_no_lower_package_imports_or_requires_the_surface() -> None:
    """Rule 1: no Lean file or lakefile of another package names the surface."""
    modules = surface_modules()
    found = []
    for package in sorted(path for path in PACKAGES.iterdir() if path.is_dir() and path != SURFACE):
        found += [f"{path.relative_to(ROOT)}: {name}" for path in lean_files(package)
                  for name in imports(path) if name in modules]
        found += [str(path.relative_to(ROOT)) for path in package.glob("lakefile.*")
                  if re.search(r"\.\./belay\b(?!-)", path.read_text())]
    assert found == []


def test_the_surface_imports_only_the_model_roots_and_lean() -> None:
    """Rule 2: every import of a surface file is its own module, a model root, or a Lean library."""
    modules = surface_modules()
    found = [f"{path.relative_to(ROOT)}: {name}" for path in lean_files(SURFACE) if path.name != "lakefile.lean"
             for name in imports(path)
             if name not in modules and name not in MODEL_ROOTS and name.split(".")[0] not in EXTERNAL_ROOTS]
    assert found == []


SURFACE_SUITE = "tests.nix"
"""The Nix file of the test suites, whose `surface` suite builds its runtime root from the
surface package; any line of it may name the surface."""
SURFACE_BUILD_LINES = frozenset({
    "sources.nix: surface = let folder = root + /packages/belay; in fs.toSource {",
    "default.nix: surfacePackage = leanPackage {",
    'default.nix: directory = "packages/belay";',
    "default.nix: source = sources.surface;",
    "default.nix: inherit leanPackages surfacePackage;",
})
"""The other lines of `build-support/` that may name the surface: its sources, its derivation,
and the argument that passes it to the test suites."""


def test_only_the_surface_build_and_its_suite_name_the_surface() -> None:
    """Rule 3: in `build-support/`, only the lines of `SURFACE_BUILD_LINES` and the test suites'
    file name the surface, so the conformance runtime does not contain it."""
    lines = [f"{path.name}: {line.strip()}" for path in sorted((ROOT / "build-support").glob("*.nix"))
             for line in path.read_text().splitlines() if SURFACE_NAMES.search(line)]
    assert [line for line in lines if not line.startswith(SURFACE_SUITE + ": ") and line not in SURFACE_BUILD_LINES] == []
    assert "default.nix: surfacePackage = leanPackage {" in lines
