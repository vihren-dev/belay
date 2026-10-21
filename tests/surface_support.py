"""The `lean` command of the surface suite's tests for a file that imports `Belay` (ADR 0017, S1).

The runtime root of the `surface` suite holds the built package, the model and the parser
library (`build-support/tests.nix`). The command gives `lean` the options that Lake's
`setup-file` gives the editor's server for such a file: the shim library as a dynamic library
and the package's shared library as a plugin, which links the parser library.
"""

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
