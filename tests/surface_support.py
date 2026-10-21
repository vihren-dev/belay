"""The `lean` command of the surface suite's tests for a file that imports `Belay`, and the
binding of candidate B's library (ADR 0017, S1).

The runtime root of the `surface` suite holds the built package, the model, the parser library
and candidate B (`build-support/tests.nix`). The command gives `lean` the module setup that Lake's
`setup-file` gives the editor's server for such a file: the file of each module, because `lean`
with a search path looks for the modules under `Belay` only in the first folder that has a
`Belay` folder, and the shared libraries that the surface's precompiled modules need.
"""

import ctypes
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/surface"
"""The Lean files that the tests elaborate."""
SUFFIX = ".dylib" if sys.platform == "darwin" else ".so"
"""The file suffix of a shared library on this platform."""


def module_setup(runtime_root: Path, directory: Path, library: Path | None = None) -> Path:
    """Write the module setup of `lake setup-file` for a file that imports `Belay` to `directory`, and
    give its path: the `.olean` file of each module of the surface, the text package and the model,
    and the shared libraries to load, in Lake's order: the model's, the shim's, the text package's
    and the surface's, or `library` in place of the text package's."""
    modules: dict[str, list[list[str]]] = {}
    for package in ("belay-sqlite-model", "belay-sqlite-text", "belay"):
        folder = runtime_root / f"packages/{package}/.lake/build/lib/lean"
        for olean in sorted(folder.rglob("*.olean")):
            modules[".".join(olean.relative_to(folder).with_suffix("").parts)] = [[str(olean)]]
    libraries = runtime_root / "packages/belay/.lake/build/lib"
    dynlibs = [libraries / f"libbelaySqliteModel_Belay_Sqlite_Model{SUFFIX}", libraries / f"libbelayParserShim{SUFFIX}",
               library or libraries / f"libbelaySqliteText_BelaySqliteText{SUFFIX}", libraries / f"libbelay_Belay{SUFFIX}"]
    path = directory / "setup.json"
    path.write_text(json.dumps({"name": "_unknown", "isModule": False, "importArts": modules,
                                "dynlibs": [str(item) for item in dynlibs], "plugins": [], "options": {}}))
    return path


def surface_command(runtime_root: Path, source: Path, directory: Path, library: Path | None = None) -> list[str]:
    """The `lean` command for a file that imports `Belay`, with its module setup in `directory`."""
    return [str(runtime_root / "lean/bin/lean"), f"--setup={module_setup(runtime_root, directory, library)}",
            str(source)]


def candidate_b(path: Path) -> ctypes.CDLL:
    """Load candidate B's library (`experiments/surface-s1/candidate-b/translate_b.h`) and declare
    its two functions."""
    library = ctypes.CDLL(str(path))
    library.belay_translate.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_size_t,
                                        ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(ctypes.c_size_t)]
    library.belay_translate.restype = ctypes.c_int
    library.belay_translate_free.argtypes = [ctypes.c_void_p]
    return library


def candidate_b_result(library: ctypes.CDLL, grammar: str, sql: str) -> object:
    """Candidate B's result for one text, decoded: the statements or the refusal."""
    document, length = ctypes.c_void_p(), ctypes.c_size_t()
    data = sql.encode()
    status = library.belay_translate(grammar.encode(), data, len(data), ctypes.byref(document), ctypes.byref(length))
    if status != 0:
        raise RuntimeError(f"belay_translate failed with status {status}")
    try:
        return json.loads(ctypes.string_at(document, length.value))
    finally:
        library.belay_translate_free(document)
