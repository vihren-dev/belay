"""Compile this repository's proof-design experiments and audit their named proofs.

This one-shot check records Nix experiment evidence, not a production CI suite.
Only the standard logical axioms are allowed in the explicitly printed proofs.
Each Lean subprocess has a fixed deadline; a compiler error or warning fails.
"""

from graphlib import TopologicalSorter
import json
from pathlib import Path
import re
import subprocess
import sys


STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
"""The existing model-test trust policy, applied to experiment proof closures."""

COMPILE_SECONDS = 90
"""The deadline for one small experiment module; timeout is a failed check."""


def inventory_counts(model: Path) -> dict[str, int]:
    """Check inventoried declaration spans against the model used by the proofs."""
    inventory = json.loads(Path("inventory.json").read_text())
    counts = {"run": 0, "statement": 0, "span_lines": 0, "pure_module_lines": 0}
    names: set[str] = set()
    for row in inventory["declarations"]:
        source = (model / "Belay/Sqlite/Model" / f"{row['module']}.lean").read_text().splitlines()
        span = source[row["start_line"] - 1:row["end_line"]]
        found = re.findall(r"^theorem (\S+)", "\n".join(span), re.MULTILINE)
        if found != [row["name"]] or len(span) != row["lines"] or row["name"] in names:
            raise RuntimeError(f"Invalid source span for {row['name']}; refresh the inventory.")
        names.add(row["name"])
        counts[row["family"]] += 1
        counts["span_lines"] += len(span)
    for module in inventory["measurement"]["pure_modules"]:
        source = (model / "Belay/Sqlite/Model" / f"{module}.lean").read_text()
        if not set(re.findall(r"^theorem (\S+)", source, re.MULTILINE)) <= names:
            raise RuntimeError(f"{module} contains a theorem outside the removal inventory.")
        counts["pure_module_lines"] += len(source.splitlines())
    return counts


def main(output: Path, model: Path) -> None:
    """Compile local imports first and retain diagnostics and each axiom report."""
    files = {path.stem: path for path in sorted(Path.cwd().glob("*.lean"))}
    if not files:
        raise RuntimeError("No experiment files found; add the Lean prototypes.")
    dependencies = {
        name: set(re.findall(r"^import (\w+)$", path.read_text(), re.MULTILINE)) & files.keys()
        for name, path in files.items()
    }
    reports: list[dict[str, object]] = []
    for name in TopologicalSorter(dependencies).static_order():
        path = files[name]
        requested = re.findall(r"^#print axioms (\S+)", path.read_text(), re.MULTILINE)
        result = subprocess.run(
            ["lean", "-o", f"{name}.olean", path.name], text=True,
            capture_output=True, timeout=COMPILE_SECONDS, check=False,
        )
        log = result.stdout + result.stderr
        (output / f"{name}.log").write_text(log)
        if result.returncode or re.search(r"\b(?:warning|error):", log):
            raise RuntimeError(f"{path.name} failed; see its log.\n{log}")
        found = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.DOTALL)
        free = re.findall(r"'([^']+)' does not depend on any axioms", log)
        if len(found) + len(free) != len(requested):
            raise RuntimeError(f"{path.name}: missing or unexpected axiom reports.\n{log}")
        closures: dict[str, list[str]] = {declaration: [] for declaration in free}
        for declaration, text in found:
            axioms = {item.strip() for item in text.split(",") if item.strip()}
            if not axioms <= STANDARD_AXIOMS:
                raise RuntimeError(f"{declaration}: unexpected axioms {sorted(axioms)}")
            closures[declaration] = sorted(axioms)
        reports.append({"module": name, "proofs": closures})
        print(f"{name}: compiled, {len(requested)} proof closures checked", flush=True)
    (output / "results.json").write_text(json.dumps(reports, indent=2) + "\n")
    (output / "inventory-counts.json").write_text(json.dumps(inventory_counts(model), indent=2) + "\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
