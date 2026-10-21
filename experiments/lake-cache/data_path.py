"""Run the ADR 0010 data path on Lake outputs: proofs project, export, verify-bundle workspace, checker.

Usage: python3 experiments/lake-cache/data_path.py WORK_DIR INSTALLATION > results.jsonl

INSTALLATION is the output of installation.nix. The verifier's own Python code (from
build/runtime) computes the generated sources and the structural record, so they are
exactly what `verify-bundle` computes. For each example:

1. a user-style proofs project (its own lakefile.toml; the contract read in place from
   an approved folder; tool-written `Generated/`) is built with Lake and cache A;
2. the bundle is exported from the project's outputs with the installed exporter;
3. `verify-bundle`'s own workspace (approved and generated modules only) is built with
   Lake and a separate cache B, as a separate trust domain would;
4. the installed bundle checker runs on that workspace's outputs and the bundle.

Each step is timed; the checker's exit code gives the status.
"""

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "build" / "runtime"))
from migration_check import cli  # noqa: E402
from migration_check.compile import EXPECTED_SOURCE  # noqa: E402
from migration_check.inputs import generated_inputs  # noqa: E402

EXAMPLES = ROOT / "examples"
CASES = {
    "small": ("3.51.0", EXAMPLES / "approved", EXAMPLES / "add_column_then_table", EXAMPLES / "approved", 0),
    "refutation": ("3.51.0", EXAMPLES / "approved", EXAMPLES / "missing_required_column", EXAMPLES / "approved", 2),
    "atuin": ("3.46.0", EXAMPLES / "atuin/approved", EXAMPLES / "atuin", EXAMPLES / "atuin", 0),
}
"""Profile, approved folder, candidate folder, schema folder and expected checker exit code."""

EXPORT_ROOTS = ("Proofs.migrationCorrect", "Proofs.migrationViolated",
                "NextInterpretation.next", "NextInterpretation.failures")
"""The same roots as `migration_check/prepare.py`."""

COMMAND_TIMEOUT_SECONDS = 600
"""Deadline for one Lake build, export or checker run."""

LIBRARY_PREFIXES = ("SqliteVerifier", "Belay")
"""Module prefixes served by the installation's library packages."""


def lean_modules(folder: Path) -> list[str]:
    """Module names of the `.lean` files directly in a folder."""
    return sorted(path.stem for path in folder.glob("*.lean"))


def lakefile(name: str, installation: Path, libraries: list[tuple[str, str, list[str]]]) -> str:
    """A TOML lakefile with the cache enabled and the installed library package required."""
    text = (f'name = "{name}"\ndefaultTargets = {json.dumps([lib for lib, _, _ in libraries])}\n'
            'enableArtifactCache = true\nrestoreAllArtifacts = true\n\n'
            f'[[require]]\nname = "sqliteVerifier"\npath = "{installation}/packages/sqlite-verifier"\n')
    for library, source, roots in libraries:
        text += f'\n[[lean_lib]]\nname = "{library}"\nsrcDir = "{source}"\nroots = {json.dumps(roots)}\n'
    return text


def run(command: list[str], directory: Path, environment: dict[str, str]) -> tuple[float, subprocess.CompletedProcess[str]]:
    """Run one command; return its wall time and result."""
    started = time.perf_counter()
    result = subprocess.run(command, cwd=directory, env=environment, capture_output=True, text=True,
                            timeout=COMMAND_TIMEOUT_SECONDS)
    return time.perf_counter() - started, result


def lake_build(directory: Path, cache: Path, installation: Path) -> tuple[float, int]:
    """Build a workspace; return wall time and the number of workspace modules compiled."""
    environment = {**os.environ, "LAKE_CACHE_DIR": str(cache), "PATH": f"{installation}/lean/bin:{os.environ['PATH']}"}
    seconds, result = run(["lake", "build"], directory, environment)
    if result.returncode:
        raise SystemExit(f"lake build failed in {directory}:\n{result.stdout[-3000:]}\n"
                         "Correct the reported error, then run the script again.")
    compiled = sum(1 for line in result.stdout.splitlines()
                   if "Built " in line and not any(f"Built {p}" in line for p in LIBRARY_PREFIXES))
    return seconds, compiled


def library_imports(folders: list[Path]) -> set[str]:
    """Library modules imported by the `.lean` files of the given folders (header lines only)."""
    found: set[str] = set()
    for folder in folders:
        for path in folder.glob("*.lean"):
            for line in path.read_text(encoding="utf-8").splitlines():
                match = re.match(r"import\s+(\S+)", line)
                if match and match.group(1).startswith(LIBRARY_PREFIXES):
                    found.add(match.group(1))
    return found


def case_run(name: str, work: Path, installation: Path) -> dict[str, object]:
    """Run the four steps for one example and report times, compile counts and the checker's exit code."""
    profile, approved, candidate, schema, expected = CASES[name]
    base = work / name
    shutil.rmtree(base, ignore_errors=True)
    common = ["--profile", profile, "--schema", str(schema / "schema.sql"),
              "--requirements", str(approved / "Requirements.lean"),
              "--interpretation", str(approved / "Interpretation.lean"), "--migration", str(candidate / "migration.sql")]
    inputs = generated_inputs(cli.arguments(["verify-bundle", *common, "--bundle", str(base / "unused")]))

    contract = base / "approved"
    shutil.copytree(approved, contract, ignore=shutil.ignore_patterns("*.sql", "*.json"))
    proofs = base / "proofs"
    (proofs / "Generated").mkdir(parents=True)
    for module, text in (("SchemaInputs", inputs.schema_source), ("SqlInputs", inputs.sql_source),
                         ("Generated", EXPECTED_SOURCE)):
        (proofs / "Generated" / f"{module}.lean").write_text(text, encoding="utf-8")
    for source in candidate.glob("*.lean"):
        shutil.copy(source, proofs / source.name)
    shutil.copy(installation / "packages/sqlite-verifier/lean-toolchain", proofs / "lean-toolchain")
    (proofs / "lakefile.toml").write_text(lakefile("proofs", installation, [
        ("Contract", "../approved", lean_modules(contract)),
        ("GeneratedInputs", "Generated", ["SchemaInputs", "SqlInputs", "Generated"]),
        ("Candidate", ".", lean_modules(proofs))]))
    build_seconds, compiled = lake_build(proofs, work / "cache-agent", installation)

    sysroot = installation / "lean"
    libraries = [installation / "packages/sqlite-verifier/.lake/build/lib/lean",
                 installation / "packages/belay-sqlite-model/.lake/build/lib/lean"]
    trusted_imports = library_imports([contract, proofs / "Generated", proofs])
    bundle = base / "proof.bundle"
    search = [sysroot / "lib/lean", *libraries, proofs / ".lake/build/lib/lean"]
    with bundle.open("w", encoding="utf-8") as stream:
        stream.write(json.dumps({"bundle": 1, "trusted_imports": sorted(trusted_imports)}) + "\n")
        stream.flush()
        started = time.perf_counter()
        exported = subprocess.run(
            [str(installation / "bin/migration-proof-exporter"),
             *[f"--omit={module}" for module in sorted(trusted_imports | {"SqliteVerifier"})],
             "--ignore-missing", "Proofs", "--", *EXPORT_ROOTS],
            env={"LEAN_SYSROOT": str(sysroot), "PATH": os.environ["PATH"], "LEAN_PATH": os.pathsep.join(map(str, search))},
            stdout=stream, stderr=subprocess.PIPE, text=True, timeout=COMMAND_TIMEOUT_SECONDS)
        export_seconds = time.perf_counter() - started
    if exported.returncode:
        raise SystemExit(f"export failed for {name}: {exported.stderr[-2000:]}\nCorrect the error, then run again.")

    verifier = base / "verify-bundle"
    (verifier / "Generated").mkdir(parents=True)
    shutil.copytree(contract, verifier / "approved")
    (verifier / "Generated" / "SchemaInputs.lean").write_text(inputs.schema_source, encoding="utf-8")
    shutil.copy(installation / "packages/sqlite-verifier/lean-toolchain", verifier / "lean-toolchain")
    (verifier / "lakefile.toml").write_text(lakefile("verification", installation, [
        ("Contract", "approved", lean_modules(contract)),
        ("GeneratedInputs", "Generated", ["SchemaInputs"])]))
    contract_seconds, contract_compiled = lake_build(verifier, work / "cache-verifier", installation)

    structural = base / "generated.json"
    structural.write_text(json.dumps(inputs.structural), encoding="utf-8")
    check_seconds, checked = run([str(installation / "bin/migration-bundle-checker"), *map(str, libraries),
                                  str(verifier / ".lake/build/lib/lean"), str(bundle), str(structural)],
                                 base, {"LEAN_SYSROOT": str(sysroot), "PATH": os.environ["PATH"]})
    return {"case": name, "expected_exit": expected, "checker_exit": checked.returncode,
            "checker_stderr": checked.stderr.strip()[-300:],
            "proofs_build_s": round(build_seconds, 3), "proofs_compiled": compiled,
            "export_s": round(export_seconds, 3), "bundle_bytes": bundle.stat().st_size,
            "verifier_build_s": round(contract_seconds, 3), "verifier_compiled": contract_compiled,
            "check_s": round(check_seconds, 3)}


if __name__ == "__main__":
    work_dir, installation_dir = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    work_dir.mkdir(parents=True, exist_ok=True)
    for case_name in CASES:
        print(json.dumps(case_run(case_name, work_dir, installation_dir)), flush=True)
