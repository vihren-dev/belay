"""Lake builds and classifications of the mutant copies of the model.

`conformance.resolve_mutants.measure` copies the `belay-sqlite-model` and `verifier-conformance`
packages, builds the import closure of `VerifierConformance.Tooling.Conformance.Classify` in each copy, and runs a
classification program with the copy. This module runs those commands with the pinned Lean
toolchain and keeps one built base for each test process.
"""

from functools import cache
import os
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory

BUILD_TIMEOUT_SECONDS = 600
"""One Lake build of a copy; a fresh base build takes about 60 seconds on 8 cores."""
RUN_TIMEOUT_SECONDS = 300
"""One interpreted classification of all case terms."""


def run(arguments: list[str], cwd: Path, lean: Path, timeout: float) -> str:
    """Run a toolchain command with only the pinned Lean on the path; raise with its output on failure."""
    result = subprocess.run(arguments, cwd=cwd, capture_output=True, text=True, timeout=timeout, check=False,
                            env={**os.environ, "PATH": f"{lean / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}",
                                 "HOME": str(cwd)})
    if result.returncode:
        raise RuntimeError(f"{' '.join(arguments)} failed in {cwd}: {result.stdout}{result.stderr}")
    return result.stdout


def build(packages: Path, lean: Path) -> None:
    """Build the case classification of the copy."""
    run(["lake", "build", "VerifierConformance.Tooling.Conformance.Classify"], packages / "verifier-conformance", lean, BUILD_TIMEOUT_SECONDS)


def classify(packages: Path, lean: Path, program: str) -> list[str]:
    """Print one verdict for each case with the built classification of the copy."""
    conformance = packages / "verifier-conformance"
    (conformance / "Classify.lean").write_text(program)
    return run(["lake", "env", "lean", "--run", "Classify.lean"], conformance, lean, RUN_TIMEOUT_SECONDS).splitlines()


def verdicts(packages: Path, lean: Path, program: str) -> list[str]:
    """Build the case classification of the copy and print one verdict for each case."""
    build(packages, lean)
    return classify(packages, lean, program)


BASE_DIRECTORIES: list[TemporaryDirectory[str]] = []
"""The directories of the built bases. Python removes them when the process ends."""


@cache
def built_base(repository: Path, lean: Path) -> Path:
    """The two packages of `repository`, copied without build outputs and built once for the
    process. Every measurement of the process copies its mutants from this base, so a test suite
    builds the unchanged model once and not once for each test. After the build, only the
    classification program of a measurement changes in the base."""
    directory = TemporaryDirectory(prefix="resolve-mutants-base-")
    BASE_DIRECTORIES.append(directory)
    base = Path(directory.name)
    for package in ("belay-sqlite-model", "verifier-conformance"):
        shutil.copytree(repository / "packages" / package, base / package,
                        ignore=shutil.ignore_patterns(".lake", "build"))
    build(base, lean)
    return base
