"""The `lean` command of the surface suite's tests for a file that imports `Belay`, and the
binding of candidate B's library (ADR 0017, S1).

The runtime root of the `surface` suite holds the built package, the model, the parser library
and candidate B (`build-support/tests.nix`). The command gives `lean` the options that Lake's
`setup-file` gives the editor's server for such a file: the shim library as a dynamic library
and the package's shared library as a plugin, which links the parser library.
"""

import ctypes
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/surface"
"""The Lean files that the tests elaborate."""
SUFFIX = ".dylib" if sys.platform == "darwin" else ".so"
"""The file suffix of a shared library on this platform."""


def surface_command(runtime_root: Path, source: Path, plugin: Path | None = None) -> list[str]:
    """The `lean` command for a file that imports `Belay`, with the libraries that Lake loads."""
    library = runtime_root / "packages/belay/.lake/build/lib"
    return [str(runtime_root / "lean/bin/lean"), f"--load-dynlib={library / ('libbelayParserShim' + SUFFIX)}",
            f"--plugin={plugin or library / ('libbelay_Belay' + SUFFIX)}", str(source)]


def lean_path(runtime_root: Path) -> dict[str, str]:
    """The environment with the surface's and the model's Lean libraries on the search path."""
    paths = [runtime_root / "packages/belay/.lake/build/lib/lean",
             runtime_root / "packages/belay-sqlite-model/.lake/build/lib/lean"]
    return {**os.environ, "LEAN_PATH": os.pathsep.join(map(str, paths))}


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
