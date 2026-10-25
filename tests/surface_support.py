"""The `lean` command of the surface suite's tests for a file that imports `Belay`.

The runtime root of the `surface` suite holds the surface, its Plausible sampler, text and model
(`build-support/tests.nix`). The command gives `lean` the module setup that Lake's
`setup-file` gives the editor's server for such a file: the file of each module, because `lean`
with a search path looks for the modules under `Belay` only in the first folder that has a
`Belay` folder, and the shared libraries that the surface's precompiled modules need.
"""

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/surface"
"""The Lean files that the tests elaborate."""
SUFFIX = ".dylib" if sys.platform == "darwin" else ".so"
"""The file suffix of a shared library on this platform."""


def module_setup(runtime_root: Path, directory: Path, library: Path | None = None,
        automatic_check: bool = False, module: str = "_unknown",
        extra_modules: dict[str, list[list[str]]] | None = None) -> Path:
    """Write the module setup of `lake setup-file` for a file that imports `Belay` to `directory`, and
    give its path: each module's `.olean` and, for Lean module-mode files, its
    server/private data and IR signature/body,
    and the shared libraries to load, in Lake's order: the model's, the model codec's, the shim's, the text package's
    Plausible's and the surface's, or `library` in place of the text package's.

    The automatic SQL check (`sql.check`) is on by default and costs seconds per theorem. Fixtures
    that test other behavior switch it off here; the automatic tests set `automatic_check`.

    `module` is the name of the module that the file defines, which the server needs to turn a
    declaration location of the file into a link. `extra_modules` adds the artifacts of
    fixture modules that the file imports."""
    modules: dict[str, list[list[str]]] = {}
    for package in ("belay-sqlite-model", "belay-sqlite-text", "belay/.lake/packages/plausible", "belay"):
        folder = runtime_root / f"packages/{package}/.lake/build/lib/lean"
        for olean in sorted(folder.rglob("*.olean")):
            data = [olean] + [Path(str(olean) + suffix) for suffix in (".server", ".private")]
            ir = [olean.with_suffix(suffix) for suffix in (".ir.sig", ".ir")]
            artifacts = [[str(path) for path in data if path.is_file()]]
            if ir[0].is_file():
                artifacts.append([str(path) for path in ir if path.is_file()])
            modules[".".join(olean.relative_to(folder).with_suffix("").parts)] = artifacts
    modules.update(extra_modules or {})
    libraries = runtime_root / "packages/belay/.lake/build/lib"
    dynlibs = [libraries / f"libbelaySqliteModel_Belay_Sqlite_Model{SUFFIX}",
               libraries / f"libbelaySqliteModel_Belay_Sqlite_Model_Codec{SUFFIX}", libraries / f"libbelayParserShim{SUFFIX}",
               library or libraries / f"libbelaySqliteText_BelaySqliteText{SUFFIX}",
               libraries / f"libplausible_Plausible{SUFFIX}", libraries / f"libbelay_Belay{SUFFIX}"]
    path = directory / "setup.json"
    path.write_text(json.dumps({"name": module, "isModule": False, "importArts": modules,
                                "dynlibs": [str(item) for item in dynlibs], "plugins": [],
                                "options": {} if automatic_check else {"weak.sql.check": False}}))
    return path


def surface_command(runtime_root: Path, source: Path, directory: Path, library: Path | None = None,
        automatic_check: bool = False) -> list[str]:
    """The `lean` command for a file that imports `Belay`, with its module setup in `directory`."""
    setup = module_setup(runtime_root, directory, library, automatic_check)
    return [str(runtime_root / "lean/bin/lean"), f"--setup={setup}", str(source)]

