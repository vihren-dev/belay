"""The layer rules of the surface and the text package below it (ADR 0016, D2, amended), read
from the import lines of every Lean package and from the Nix build.

1. Nothing below the surface imports it: no Lean file of another package under `packages/`
   imports a module of `packages/belay`, and no other lakefile requires it.
2. Nothing below the text package imports it: no Lean file of a package other than the surface
   and the text package imports a module of `packages/belay-sqlite-text`, and no lakefile other
   than the surface's requires it.
3. The surface imports only its own modules, the text package's, the model's roots
   `Belay.Sqlite.Model` and `Belay.Sqlite.Model.Codec`, `Init`, `Std` and `Lean`; the text package
   imports only its own modules, the model's roots and Lean's libraries.
4. The conformance runtime does not contain the surface: in `build-support/`, only the
   surface's own derivation and the `surface` test suite name it.
"""

from pathlib import Path
import re

import pytest

pytestmark = pytest.mark.unit

ROOT = Path(__file__).resolve().parents[1]
PACKAGES = ROOT / "packages"
SURFACE = PACKAGES / "belay"
TEXT = PACKAGES / "belay-sqlite-text"
MODEL_ROOTS = {"Belay.Sqlite.Model", "Belay.Sqlite.Model.Codec"}
"""The model's root modules, the only model modules that the surface and the text package may import."""
EXTERNAL_ROOTS = {"Init", "Std", "Lean"}
"""The Lean libraries that the surface and the text package may import."""
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


def modules(package: Path) -> set[str]:
    """The modules of a package, without its lakefile."""
    return {module_name(package, path) for path in lean_files(package) if path.name != "lakefile.lean"}


def test_the_surface_and_the_text_package_have_modules() -> None:
    """The rules below read the packages' files; an empty set would make them pass vacuously."""
    assert {"Belay", "Belay.Sqlite"} <= modules(SURFACE)
    assert {"Belay.Sqlite.Parse", "Belay.Sqlite.Translation"} <= modules(TEXT)


@pytest.mark.parametrize("upper", [SURFACE, TEXT], ids=["surface", "text"])
def test_no_lower_package_imports_or_requires_an_upper_one(upper: Path) -> None:
    """Rules 1 and 2: no Lean file or lakefile of a package below `upper` names it; the packages
    below the text package are all but the surface and the text package."""
    names = modules(upper)
    allowed = {SURFACE, upper}
    pattern = re.compile(r"\.\./" + re.escape(upper.name) + r"(?![-\w])")
    found = []
    for package in sorted(path for path in PACKAGES.iterdir() if path.is_dir() and path not in allowed):
        found += [f"{path.relative_to(ROOT)}: {name}" for path in lean_files(package)
                  for name in imports(path) if name in names]
        found += [str(path.relative_to(ROOT)) for path in package.glob("lakefile.*") if pattern.search(path.read_text())]
    assert found == []


@pytest.mark.parametrize("package", [SURFACE, TEXT], ids=["surface", "text"])
def test_imports_are_own_modules_model_roots_and_lean(package: Path) -> None:
    """Rule 3: every import of a surface file is its own module, a text package module, a model
    root or a Lean library; every import of a text package file is its own module, a model root or a
    Lean library."""
    allowed = modules(package) | (modules(TEXT) if package == SURFACE else set())
    found = [f"{path.relative_to(ROOT)}: {name}" for path in lean_files(package) if path.name != "lakefile.lean"
             for name in imports(path)
             if name not in allowed and name not in MODEL_ROOTS and name.split(".")[0] not in EXTERNAL_ROOTS]
    assert found == []


SURFACE_SUITE = "tests.nix"
"""The Nix file of the test suites, whose `surface` suite builds its runtime root from the
surface package; any line of it may name the surface."""
SURFACE_BUILD_LINES = frozenset({
    "sources.nix: surface = let folder = root + /packages/belay; in fs.toSource {",
    "default.nix: surfacePackage = leanPackage {",
    'default.nix: directory = "packages/belay";',
    "default.nix: source = sources.surface;",
    "default.nix: inherit leanPackages surfacePackage textPackage;",
})
"""The other lines of `build-support/` that may name the surface: its sources, its derivation,
and the argument that passes it to the test suites."""


def test_only_the_surface_build_and_its_suite_name_the_surface() -> None:
    """Rule 4: in `build-support/`, only the lines of `SURFACE_BUILD_LINES` and the test suites'
    file name the surface, so the conformance runtime does not contain it."""
    lines = [f"{path.name}: {line.strip()}" for path in sorted((ROOT / "build-support").glob("*.nix"))
             for line in path.read_text().splitlines() if SURFACE_NAMES.search(line)]
    assert [line for line in lines if not line.startswith(SURFACE_SUITE + ": ") and line not in SURFACE_BUILD_LINES] == []
    assert "default.nix: surfacePackage = leanPackage {" in lines
