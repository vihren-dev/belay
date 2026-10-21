"""Print the import graph facts that decide incremental rebuild cost.

For each Lean module in the given package directories, count the modules that import
it directly or transitively (its rebuild fan-out). With --closure ROOT, also list the
modules in ROOT's import closure whose name contains a given marker (for example
`.Spec` or `Laws`), and the import edges that bring them in from other modules.

Usage: python3 -I import_graph.py PACKAGE_DIR... [--closure ROOT] [--marker TEXT]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", re.MULTILINE)


def module_files(directories: list[Path]) -> dict[str, Path]:
    """Map each module name to its source file, from the package directories."""
    modules: dict[str, Path] = {}
    for directory in directories:
        for path in directory.rglob("*.lean"):
            if ".lake" in path.parts:
                continue
            modules[".".join(path.relative_to(directory).with_suffix("").parts)] = path
    return modules


def import_graph(modules: dict[str, Path]) -> dict[str, list[str]]:
    """Return the imports of each module that are themselves in the packages."""
    return {name: [m for m in IMPORT.findall(path.read_text()) if m in modules] for name, path in modules.items()}


def closure(graph: dict[str, list[str]], root: str) -> set[str]:
    """Return the modules that root imports, directly or transitively, and root."""
    seen, stack = set(), [root]
    while stack:
        module = stack.pop()
        if module not in seen:
            seen.add(module)
            stack.extend(graph.get(module, []))
    return seen


def main(arguments: list[str]) -> None:
    """Print fan-out counts and, with --closure, the marked modules of a closure."""
    options = {arguments[i]: arguments[i + 1] for i, a in enumerate(arguments) if a.startswith("--")}
    directories = [Path(a) for i, a in enumerate(arguments) if not a.startswith("--") and (i == 0 or not arguments[i - 1].startswith("--"))]
    graph = import_graph(module_files(directories))
    reverse: dict[str, set[str]] = {m: set() for m in graph}
    for module in graph:
        for dependency in closure(graph, module) - {module}:
            reverse[dependency].add(module)
    root = options.get("--closure")
    scope = closure(graph, root) if root else set(graph)
    print(f"modules {len(graph)}, in scope {len(scope)}")
    print("largest fan-out in scope (dependents in scope):")
    for module in sorted(scope, key=lambda m: -len(reverse[m] & scope))[:12]:
        print(f"  {len(reverse[module] & scope):4}  {module}")
    marker = options.get("--marker")
    if root and marker:
        marked = sorted(m for m in scope if marker in m)
        print(f"\n{len(marked)} modules in the closure of {root} contain '{marker}'. Edges into them from unmarked modules:")
        for module in sorted(scope):
            if marker not in module:
                for dependency in graph[module]:
                    if marker in dependency:
                        print(f"  {module} -> {dependency}")


if __name__ == "__main__":
    main(sys.argv[1:])
