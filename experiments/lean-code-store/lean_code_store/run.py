"""Command line of the prototype: extract the file versions that the local store lacks.

Example, from the repository root with the dev shell loaded:

    PYTHONPATH=.:experiments/lean-code-store python3 -m lean_code_store.run \
        --package packages/belay-sqlite-model=/nix/store/...-belay-sqlite-model-0.1.0=Belay \
        --library /nix/store/...-plausible-0.1.0/.lake/build/lib/lean \
        --store build/lean-code-store --reader experiments/lean-code-store/extractor/.lake/build/bin/lean-code-store-facts
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from functools import lru_cache
import json
from pathlib import Path
import shutil
import time
import uuid

from lean_code_store.facts import module_facts
from lean_code_store.folding import Declaration, decide_module
from lean_code_store.resolve import resolver
from lean_code_store.inputs import key_input, lean_version, read_facts, select_files
from lean_code_store.keys import dependency_order, snapshot_keys
from lean_code_store.mentions import read_usages
from lean_code_store.rows import build_rows
from lean_code_store.store import LocalStore
from tools.theorem_dependency_manifest import merge_libraries

EXTRACTOR_VERSION = "lean-code-store-prototype-7"
"""Changes with each change to what the extractor writes, so that all keys change."""


def run(packages: list[tuple[str, Path, str]], libraries: list[Path], store: LocalStore,
        lean: Path, reader: Path, workers: int, project: str, work: Path) -> dict[str, object]:
    """Extract each selected file version without a `files` row, then write the snapshot."""
    started = time.monotonic()
    files = {file.module: file for file in select_files(packages)}
    project_libraries = [file.library for file in files.values()]
    inputs = {module: key_input(file, project_libraries, set(files)) for module, file in files.items()}
    keys = snapshot_keys(EXTRACTOR_VERSION, lean_version(lean), inputs)
    order = dependency_order(inputs)
    missing = [module for module in order if not store.is_complete(keys[module])]
    keyed = time.monotonic()
    if work.exists():
        shutil.rmtree(work)
    library = work / "lib"
    merge_libraries(sorted(set(project_libraries)) + libraries, library)
    seconds = read_facts(reader, library, {m: files[m].source for m in missing}, work / "facts", workers) if missing else {}
    read = time.monotonic()

    @lru_cache(maxsize=None)
    def fold_of(file_key: str) -> dict[str, list[str] | None]:
        return store.fold(file_key)

    def imported(module: str, name: str) -> Declaration | None:
        folded = fold_of(keys[module]).get(name, [module, name])
        return (folded[0], folded[1]) if folded is not None else None

    for module in missing:
        file = files[module]
        facts = module_facts(json.loads((work / "facts" / f"{module}.json").read_text()), module)
        source = file.source.read_text()
        decisions = decide_module(facts, source)
        resolve = resolver(facts, decisions, imported, lambda m: m in files)
        ilean = file.library.joinpath(*module.split(".")).with_suffix(".ilean").read_text()
        rows = build_rows(keys[module], facts, decisions, source, read_usages(ilean), resolve)
        fold = {c.name: (list(folded) if (folded := resolve(module, c.name)) else None)
                for c in facts.constants}
        store.write_version(keys[module], rows, fold)
    snapshot_id = str(uuid.uuid4())
    store.write_snapshot(
        {"snapshot_id": snapshot_id, "project": project,
         "created_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S.%f")},
        [{"snapshot_id": snapshot_id, "source_path": files[m].source_path, "module_name": m,
          "file_key": keys[m]} for m in sorted(files)])
    return {"snapshot_id": snapshot_id, "files": len(files), "extracted": len(missing),
            "extracted_modules": missing if len(missing) <= 50 else len(missing),
            "seconds": {"keys": round(keyed - started, 2), "fact_reader_wall": round(read - keyed, 2),
                        "fact_reader_sum": round(sum(seconds.values()), 2),
                        "fact_reader_max": round(max(seconds.values(), default=0.0), 2),
                        "rows": round(time.monotonic() - read, 2),
                        "total": round(time.monotonic() - started, 2)},
            "counts": dict(sum((Counter(json.loads((store.version(keys[m]) / "counts.json").read_text())
                                        ["counts"]) for m in files), Counter()))}


def package_argument(value: str) -> tuple[str, Path, str]:
    """Read `PATH=DIRECTORY=TREE`."""
    parts = value.split("=")
    if len(parts) != 3 or not all(parts):
        raise argparse.ArgumentTypeError(f"{value!r} is not PATH=DIRECTORY=TREE")
    return parts[0], Path(parts[1]), parts[2]


def main() -> int:
    """Parse the arguments, run, and print the summary as JSON."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--package", type=package_argument, action="append", required=True,
                        help="A built package PATH=DIRECTORY=TREE: its path in the project, the directory of "
                             "the build, and its library tree; give it once for each package")
    parser.add_argument("--library", type=Path, action="append", default=[],
                        help="A compiled library directory of a third-party package")
    parser.add_argument("--store", type=Path, required=True)
    parser.add_argument("--reader", type=Path, required=True, help="The lean-code-store-facts executable")
    parser.add_argument("--lean", type=Path, default=Path(shutil.which("lean") or "lean"))
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--project", default="belay")
    arguments = parser.parse_args()
    store = LocalStore(arguments.store)
    summary = run(arguments.package, arguments.library, store, arguments.lean, arguments.reader,
                  arguments.workers, arguments.project, arguments.store / "work")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
