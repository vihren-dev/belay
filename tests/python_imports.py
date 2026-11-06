"""The local Python modules that a test file can import, for the checks of Nix suite inputs.

A Nix suite gets only the files that it declares, so that a change to another file leaves its
cached result valid. `tests/test_conformance_frontend.py` and `tests/test_mutant_suite_inputs.py`
compare the declared modules with the import closure that this module computes on the host.
"""

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCAL_PACKAGES = ("belay", "conformance", "tests", "tools")
"""Repository packages whose imports are followed; other imports are standard or pinned libraries."""


def imported_modules(path: Path, root: Path = ROOT) -> set[str]:
    """Local modules that one file imports, so that the closure can follow them.

    `from package import name` may import a submodule, so the candidate `package.name`
    is included when it is a module file. Imports inside functions count too, because
    they run when the function runs.
    """
    package = ".".join(path.relative_to(root).parts[:-1])
    names: set[str] = set()
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if isinstance(node, ast.ImportFrom):
            base = node.module or ""
            if node.level:
                parent = ".".join(package.split(".")[:len(package.split(".")) - node.level + 1])
                base = f"{parent}.{base}" if base else parent
            names.add(base)
            names.update(f"{base}.{alias.name}" for alias in node.names
                         if module_file(f"{base}.{alias.name}", root) is not None)
        elif isinstance(node, ast.Import):
            names.update(alias.name for alias in node.names)
    return {name for name in names if name.split(".")[0] in LOCAL_PACKAGES}


def module_file(name: str, root: Path = ROOT) -> Path | None:
    """The file that defines a local module, which the closure reads next; None for other names."""
    path = root / (name.replace(".", "/") + ".py")
    return path if path.is_file() else None


def import_closure(test_files: list[str], root: Path = ROOT) -> set[str]:
    """Every local module that a suite's tests can import, which its Nix inputs must contain."""
    pending = [name for file in test_files for name in imported_modules(root / file, root)]
    reached: set[str] = set()
    while pending:
        name = pending.pop()
        path = module_file(name, root)
        if name in reached or path is None:
            continue
        reached.add(name)
        pending.extend(imported_modules(path, root))
    return reached
