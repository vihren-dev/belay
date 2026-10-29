"""Compile the proof-boundary experiments and audit their declared proof closures.

This explicit research check retains compiler diagnostics and exact package inputs.
It is not a production test suite. All compiler subprocesses have fixed deadlines.
"""

from graphlib import TopologicalSorter
import json
from pathlib import Path
import re
import subprocess
import sys

from imports import check_imports


STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
"""The existing model trust policy for every explicitly audited closure."""


def compile_file(path: Path, output: Path) -> dict[str, list[str]]:
    """Compile a prototype, reject diagnostics, and verify its requested audits."""
    requested = re.findall(r"^#print axioms (\S+)", path.read_text(), re.MULTILINE)
    result = subprocess.run(
        ["lean", "-o", str(path.with_suffix(".olean")), str(path)],
        capture_output=True, text=True, timeout=120, check=False,
    )
    log = result.stdout + result.stderr
    (output / f"{path.stem}.log").write_text(log)
    if result.returncode or re.search(r"\b(?:warning|error)(?:\([^)]*\))?:", log):
        raise RuntimeError(f"{path.name} failed.\n{log}")
    reports = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.DOTALL)
    free = re.findall(r"'([^']+)' does not depend on any axioms", log)
    closures: dict[str, list[str]] = {name: [] for name in free}
    for name, text in reports:
        axioms = {part.strip() for part in text.split(",") if part.strip()}
        if not axioms <= STANDARD_AXIOMS:
            raise RuntimeError(f"{name}: forbidden axioms {sorted(axioms)}")
        closures[name] = sorted(axioms)
    # Some probes print inside their namespace, so Lean reports qualified names.
    if len(closures) != len(requested) or any(
        not any(name == request or name.endswith("." + request) for name in closures)
        for request in requested
    ):
        raise RuntimeError(f"{path.name}: missing or duplicate requested proof audits")
    print(f"{path.stem}: compiled, {len(closures)} closures checked", flush=True)
    return closures


def main(output: Path, model: Path, surface: Path, text: Path) -> None:
    """Build prototypes in dependency order and retain import-narrowing evidence."""
    files = {path.stem: path for path in sorted(Path.cwd().glob("*.lean"))}
    if not files:
        raise RuntimeError("No Lean experiments found")
    dependencies = {
        name: set(re.findall(r"^import (\w+)$", path.read_text(), re.MULTILINE)) & files.keys()
        for name, path in files.items()
    }
    reports = {}
    for name in TopologicalSorter(dependencies).static_order():
        reports[name] = compile_file(files[name], output)
    combined = Path("Combined.lean")
    combined.write_text("".join(f"import {name}\n" for name in files))
    reports["Combined"] = compile_file(combined, output)
    (output / "proofs.json").write_text(json.dumps(reports, indent=2) + "\n")
    check_imports(output, model, surface, text)


if __name__ == "__main__":
    main(*(Path(value) for value in sys.argv[1:]))
