"""The imperative inputs of a run: the selection, the build products and the fact reader.

The selection is the library trees of the packages, as the dependency report selects them.
The build products come from the library directories of one completed build.
"""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import json
import os
from pathlib import Path
import subprocess
import time

from lean_code_store.keys import KeyInput, sha256_hex

FACT_READER_TIMEOUT_SECONDS = 300
"""Bound of the fact reader for one module; the largest module of the tree needs about 1 s."""


@dataclass(frozen=True)
class SelectedFile:
    """One selected source file with its build products."""

    module: str
    source_path: str
    """Relative to the project root, with `/` as separator."""
    source: Path
    library: Path
    """The library directory that contains the build products of the module."""


def select_files(packages: list[tuple[str, Path, str]]) -> list[SelectedFile]:
    """Each `.lean` file of each package tree, and the tree's umbrella.

    A package is `(path in the project, directory, tree)`; the path is `.` for the project root.
    """
    selected: list[SelectedFile] = []
    for name, directory, tree in packages:
        root = directory / tree
        if not root.is_dir():
            raise ValueError(f"{root}: library tree is missing; give the directory of a built package")
        sources = sorted(root.rglob("*.lean"))
        if (directory / f"{tree}.lean").is_file():
            sources.append(directory / f"{tree}.lean")
        for source in sources:
            relative = source.relative_to(directory)
            selected.append(SelectedFile(
                module=".".join(relative.with_suffix("").parts),
                source_path=(Path(name) / relative).as_posix(), source=source,
                library=directory / ".lake" / "build" / "lib" / "lean"))
    modules = [file.module for file in selected]
    if len(set(modules)) != len(modules):
        raise ValueError("Two selected files have the same module name; select each package once")
    return sorted(selected, key=lambda file: file.module)


REQUIRED_PRODUCTS = (".ilean", ".olean")
"""Build products that each module has; they are inputs of its key."""

OPTIONAL_PRODUCTS = (".olean.server", ".olean.private")
"""The `.olean` parts that Lake writes only for a file of the module system; inputs when present."""


def product_paths(file: SelectedFile) -> list[Path]:
    """The `.ilean` file and each `.olean` part that Lake wrote for the module, by file name."""
    base = file.library.joinpath(*file.module.split("."))
    required = [base.with_name(base.name + suffix) for suffix in REQUIRED_PRODUCTS]
    missing = [path.name for path in required if not path.is_file()]
    if missing:
        raise ValueError(f"{file.module}: build products {missing} are missing in {file.library}; "
                         "build the module")
    optional = [base.with_name(base.name + suffix) for suffix in OPTIONAL_PRODUCTS]
    return sorted(required + [path for path in optional if path.is_file()], key=lambda path: path.name)


def key_input(file: SelectedFile, project_libraries: list[Path], selected: set[str]) -> KeyInput:
    """The key input of one file. An unselected import of the project's own packages fails."""
    products = product_paths(file)
    ilean = json.loads(next(path for path in products if path.suffix == ".ilean").read_text())
    imports = tuple(sorted({str(entry[0]) for entry in ilean.get("directImports", [])}))
    for module in imports:
        if module in selected:
            continue
        olean = Path(*module.split(".")).with_suffix(".olean")
        if any((library / olean).is_file() for library in project_libraries):
            raise ValueError(f"{file.module} imports {module}, a module of the project that is not "
                             "selected; add its package to the selection")
    return KeyInput(module_name=file.module, text_sha256=sha256_hex(file.source.read_bytes()),
                    products=tuple((path.name, sha256_hex(path.read_bytes())) for path in products),
                    imports=imports)


def lean_version(lean: Path) -> str:
    """The output of `lean --version` of the toolchain that built the tree."""
    return subprocess.run([str(lean), "--version"], check=True, text=True, capture_output=True,
                          timeout=60).stdout.strip()


def read_facts(reader: Path, lean_path: Path, modules: dict[str, Path], output: Path,
               workers: int) -> dict[str, float]:
    """Run the fact reader once for each module and its source file, `workers` at a time.

    The result gives the seconds of each module.
    """
    output.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ, LEAN_PATH=str(lean_path))

    def one(module: str) -> tuple[str, float]:
        started = time.monotonic()
        result = subprocess.run([str(reader), module, str(modules[module]), str(output / f"{module}.json")],
                                env=environment, text=True, capture_output=True,
                                timeout=FACT_READER_TIMEOUT_SECONDS)
        if result.returncode != 0:
            raise ValueError(f"Fact reader failed for {module}: {result.stderr.strip()}")
        return module, time.monotonic() - started

    with ThreadPoolExecutor(max_workers=workers) as pool:
        return dict(pool.map(one, modules))
