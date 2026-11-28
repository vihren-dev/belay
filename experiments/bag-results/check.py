"""Compile the bag-results experiment, audit its proofs, and run its measurements.

This research check builds every Lean file of the experiment with the pinned toolchain and the
pinned model package, in import order. It fails on any warning or error, so a `sorry` fails it.
Each `#print axioms` line names a main theorem; the check fails when a theorem depends on an
axiom other than `propext`, `Classical.choice` and `Quot.sound`. Then it runs the native probes
with the pinned SQLite and measures the kernel cost of two bag representations. It is not a
production test suite. All subprocesses have fixed deadlines.
"""

from graphlib import TopologicalSorter
import json
from pathlib import Path
import re
import subprocess
import sys

import kernel_cost

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
"""The model's trust policy for every audited theorem."""

COMPILE_DEADLINE_SECONDS = 300
"""The deadline for one Lean file of the experiment; the slowest one takes a few seconds."""

PROBES_DEADLINE_SECONDS = 120
"""The deadline for the probe script, which gives sqlite3 itself 60 seconds."""


def module_name(path: Path) -> str:
    """The Lean module name of a file under the working directory."""
    return ".".join(path.with_suffix("").parts)


def compile_file(path: Path, output: Path) -> dict[str, list[str]]:
    """Compile one file, reject diagnostics, and return the axioms of its audited theorems."""
    requested = re.findall(r"^#print axioms (\S+)", path.read_text(), re.MULTILINE)
    result = subprocess.run(
        ["lean", "-o", str(path.with_suffix(".olean")), str(path)],
        capture_output=True, text=True, timeout=COMPILE_DEADLINE_SECONDS,
        check=False,
    )
    log = result.stdout + result.stderr
    (output / f"{module_name(path)}.log").write_text(log)
    if result.returncode or re.search(r"\b(?:warning|error)(?:\([^)]*\))?:", log):
        raise RuntimeError(f"{path} failed.\n{log}")
    reports = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.DOTALL)
    free = re.findall(r"'([^']+)' does not depend on any axioms", log)
    closures: dict[str, list[str]] = {name: [] for name in free}
    for name, text in reports:
        axioms = {part.strip() for part in text.split(",") if part.strip()}
        forbidden = axioms - STANDARD_AXIOMS
        if forbidden:
            raise RuntimeError(f"{path}: {name} depends on the forbidden axioms "
                               f"{sorted(forbidden)}; remove them from its proof")
        closures[name] = sorted(axioms)
    if len(closures) != len(requested):
        raise RuntimeError(f"{path}: missing or duplicate axiom audits")
    print(f"{module_name(path)}: compiled, {len(closures)} theorems audited", flush=True)
    return closures


def main(output: Path, sqlite: str) -> None:
    """Build the Lean files in import order, then run the probes and the cost measurement."""
    files = {module_name(path): path for path in sorted(Path(".").rglob("*.lean"))
             if "kernel-cost" not in path.parts}
    if not files:
        raise RuntimeError("No Lean files found")
    dependencies = {
        name: set(re.findall(r"^import (\S+)$", path.read_text(), re.MULTILINE)) & files.keys()
        for name, path in files.items()
    }
    audits = {name: compile_file(files[name], output)
              for name in TopologicalSorter(dependencies).static_order()}
    (output / "proofs.json").write_text(json.dumps(audits, indent=2) + "\n")
    subprocess.run(["bash", "probes/run-probes.sh", sqlite], timeout=PROBES_DEADLINE_SECONDS,
                   check=True)
    print("probes: output equals probes/probes.expected", flush=True)
    kernel_cost.main(output)


if __name__ == "__main__":
    main(Path(sys.argv[1]), sys.argv[2])
