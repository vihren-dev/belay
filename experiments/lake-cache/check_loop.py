"""Measure the proof author's loop and test a prototype audit command (ADR 0010 section 10).

Usage: python3 experiments/lake-cache/check_loop.py WORK_DIR INSTALLATION EDITS > results.jsonl

Run data_path.py WORK_DIR INSTALLATION first; this script reuses its proofs projects.
It adds a prototype audit command (`BelayAudit.lean`, which imports `Lean`) and a
generated `Check` module to each project. Then it times EDITS proof edits, each followed
by `lake build` of the candidate only and of the candidate plus `Check`, and runs the
audit's failure cases on a copy of the small project.
"""

import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import sys
import time

AUDIT_SOURCE = '''import Lean
open Lean Elab Command

/-- Fail the build when the theorem uses an axiom outside the gate's allowlist (this
includes `sorryAx`), when the environment imports a module outside the allowed
prefixes, or when this module is compiled with `debug.skipKernelTC`. Prototype for
ADR 0010 section 10; the gate's allowlist is inline in `GateCore.lean`. -/
syntax (name := belayAudit) "#belay_audit " ident " allowing " "[" str,* "]" : command

@[command_elab belayAudit] def elabBelayAudit : CommandElab := fun stx => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let prefixes := stx[4].getSepArgs.filterMap (·.isStrLit?) |>.map String.toName
  let axioms ← collectAxioms name
  let rejected := axioms.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
  unless rejected.isEmpty do
    throwError "{name} depends on axioms outside the allowlist: {rejected}"
  let outside := (← getEnv).header.moduleNames.filter fun m => !prefixes.any (·.isPrefixOf m)
  unless outside.isEmpty do
    throwError "imports that the verifier does not have: {outside}"
  if (← getOptions).getBool `debug.skipKernelTC then
    throwError "debug.skipKernelTC is set"
'''

ALLOWED_PREFIXES = ["Init", "Std", "Lean", "SqliteVerifier", "Belay", "BelayAudit"]
"""Module prefixes the prototype accepts besides the project's own modules."""

BUILD_TIMEOUT_SECONDS = 600
"""Deadline for one `lake build`."""


def theorem(case: str) -> str:
    """The proved root: the refutation proves `migrationViolated`."""
    return "Proofs.migrationViolated" if case == "refutation" else "Proofs.migrationCorrect"


def add_check(proofs: Path, case: str) -> None:
    """Write the audit command and the generated `Check` module, and declare them in the lakefile."""
    modules = sorted({path.stem for folder in (proofs, proofs / "Generated", proofs.parent / "approved")
                      for path in folder.glob("*.lean")} - {"Check", "BelayAudit"})
    (proofs / "Generated" / "BelayAudit.lean").write_text(AUDIT_SOURCE, encoding="utf-8")
    allowed = ", ".join(json.dumps(name) for name in ALLOWED_PREFIXES + modules)
    (proofs / "Generated" / "Check.lean").write_text(
        f"import Proofs\nimport BelayAudit\n\n#belay_audit {theorem(case)} allowing [{allowed}]\n", encoding="utf-8")
    lakefile = proofs / "lakefile.toml"
    text = lakefile.read_text(encoding="utf-8")
    if 'name = "Check"' not in text:
        lakefile.write_text(text + '\n[[lean_lib]]\nname = "Check"\nsrcDir = "Generated"\nroots = ["BelayAudit", "Check"]\n')


def lake(proofs: Path, installation: Path, cache: Path, *targets: str) -> tuple[float, subprocess.CompletedProcess[str]]:
    """Run `lake build` on the given targets; return wall time and the result."""
    environment = {**os.environ, "LAKE_CACHE_DIR": str(cache), "PATH": f"{installation}/lean/bin:{os.environ['PATH']}"}
    started = time.perf_counter()
    result = subprocess.run(["lake", "build", *targets], cwd=proofs, env=environment, capture_output=True,
                            text=True, timeout=BUILD_TIMEOUT_SECONDS)
    return time.perf_counter() - started, result


def edit(path: Path) -> None:
    """Add a new small theorem, so the compiled module changes and its importers rebuild.

    A comment-only edit leaves the `.olean` byte-identical, and Lake then skips `Check`.
    """
    with path.open("a", encoding="utf-8") as stream:
        stream.write(f"\ntheorem edit{time.time_ns()} : True := trivial\n")


def loop(case: str, work: Path, installation: Path, edits: int) -> dict[str, object]:
    """Median build times after a proof edit: candidate only, and candidate plus `Check`."""
    proofs = work / case / "proofs"
    add_check(proofs, case)
    cache = work / "cache-agent"
    seconds, first = lake(proofs, installation, cache, "Candidate", "Check")
    if first.returncode:
        raise SystemExit(f"{case}: the audit fails on the correct proof:\n{first.stdout[-2000:]}")
    samples: dict[str, list[float]] = {"candidate_only_s": [], "candidate_and_check_s": []}
    for _ in range(edits):
        edit(proofs / "Proofs.lean")
        samples["candidate_only_s"].append(lake(proofs, installation, cache, "Candidate")[0])
        edit(proofs / "Proofs.lean")
        samples["candidate_and_check_s"].append(lake(proofs, installation, cache, "Candidate", "Check")[0])
    return {"case": case, "first_build_with_check_s": round(seconds, 3),
            **{key: round(statistics.median(values), 3) for key, values in samples.items()}}


HEADER = "import Generated\nimport SqliteVerifier.Demonstration\n\n"
"""The small example's imports."""

FAILURES = {
    "sorry": HEADER + "namespace Proofs\ntheorem migrationCorrect : Generated.expected := by sorry\nend Proofs\n",
    "custom_axiom": HEADER + "axiom cheat : False\nnamespace Proofs\n"
                    "theorem migrationCorrect : Generated.expected := cheat.elim\nend Proofs\n",
    "import_outside": "import Lake\n" + HEADER + "namespace Proofs\ntheorem migrationCorrect : Generated.expected :=\n"
                      "  SqliteVerifier.Demonstration.migrationCorrect\nend Proofs\n",
    "skip_kernel_tc": HEADER + "set_option debug.skipKernelTC true\nnamespace Proofs\n"
                      "theorem migrationCorrect : Generated.expected :=\n"
                      "  SqliteVerifier.Demonstration.migrationCorrect\nend Proofs\n",
}
"""Complete `Proofs.lean` files that each break one audit rule; the last one is a correct proof."""


def failures(work: Path, installation: Path) -> list[dict[str, object]]:
    """Copy the small project with one broken `Proofs.lean` at a time, and record what `lake build` reports."""
    results = []
    for name, text in FAILURES.items():
        base = work / f"failure-{name}"
        shutil.rmtree(base, ignore_errors=True)
        shutil.copytree(work / "small", base, symlinks=True, ignore=shutil.ignore_patterns(".lake"))
        (base / "proofs" / "Proofs.lean").write_text(text, encoding="utf-8")
        _, result = lake(base / "proofs", installation, work / "cache-agent", "Candidate", "Check")
        errors = [line[:200] for line in result.stdout.splitlines() if "error" in line][:2]
        results.append({"failure": name, "build_failed": result.returncode != 0, "errors": errors})
    return results


if __name__ == "__main__":
    work_dir, installation_dir, edit_count = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve(), int(sys.argv[3])
    for case_name in ("small", "refutation", "atuin"):
        print(json.dumps(loop(case_name, work_dir, installation_dir, edit_count)), flush=True)
    for record in failures(work_dir, installation_dir):
        print(json.dumps(record), flush=True)
