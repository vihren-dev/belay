"""Write a Lake workspace and build it with bounded resources (ADR 0010 sections 1 and 6).

`verify-bundle` compiles the approved contract and the generated inputs in a
workspace that it writes itself; `prepare` builds the user's proofs project.
Lake compiles changed modules only, in parallel, and reuses outputs from its
artifact cache. The lakefile is TOML that the verifier generates: data that Lake
reads, never code that Lake runs. The build runs as one bounded process: one
deadline, a minimal environment and limited output files (`process.run_process`).
"""

from collections.abc import Sequence
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re

from .process import run_process
from .source_closure import CompileError

MAX_PARALLEL_JOBS = 8
"""Upper bound on Lake's parallel jobs. Lake has no jobs option; it runs on Lean's thread pool, which
`LEAN_NUM_THREADS` bounds (an Atuin build took 9.0 s with one thread and 4.8 s with eight)."""

BUILD_TIMEOUT_SECONDS = 300
"""Deadline for one `lake build` of a workspace; the Atuin contract builds in about 3 s."""

FAILED_TARGET = re.compile(r"^- (\S+)$")
"""One line of Lake's 'Some required targets logged failures' list."""

BUILT_MODULE = re.compile(r"Built (\S+)")
"""A progress line for a module that Lake compiled, not replayed or restored."""


@dataclass(frozen=True)
class Library:
    """One Lake library of a workspace: its source folder (relative to the workspace) and root modules."""

    name: str
    source_dir: str
    roots: tuple[str, ...]


def lakefile(name: str, runtime_root: Path, libraries: Sequence[Library]) -> str:
    """A workspace lakefile that requires the installed runtime and enables the artifact cache."""
    lines = [f"name = {json.dumps(name)}", f"defaultTargets = {json.dumps([library.name for library in libraries])}",
             "enableArtifactCache = true", "restoreAllArtifacts = true", "",
             "[[require]]", 'name = "sqliteVerifier"', f"path = {json.dumps(str(runtime_root))}"]
    for library in libraries:
        lines += ["", "[[lean_lib]]", f"name = {json.dumps(library.name)}",
                  f"srcDir = {json.dumps(library.source_dir)}", f"roots = {json.dumps(list(library.roots))}"]
    return "\n".join(lines) + "\n"


def write_workspace(directory: Path, name: str, runtime_root: Path, libraries: Sequence[Library]) -> None:
    """Write the lakefile and the pinned toolchain file; Lake stops and asks for a restart without the latter."""
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "lakefile.toml").write_text(lakefile(name, runtime_root, libraries), encoding="utf-8")
    (directory / "lean-toolchain").write_text((runtime_root / "lean-toolchain").read_text(encoding="utf-8"),
                                             encoding="utf-8")


def compiled_modules(output: str, library_prefixes: Sequence[str]) -> tuple[str, ...]:
    """Modules that Lake compiled, without the installed libraries' modules."""
    names = (match.group(1) for match in BUILT_MODULE.finditer(output))
    return tuple(name for name in names if not name.startswith(tuple(library_prefixes)))


def failed_targets(output: str) -> tuple[str, ...]:
    """The targets that Lake lists after 'Some required targets logged failures'."""
    lines = output.splitlines()
    try:
        start = next(index for index, line in enumerate(lines) if "Some required targets logged failures" in line)
    except StopIteration:
        return ()
    failed = []
    for line in lines[start + 1:]:
        match = FAILED_TARGET.match(line.strip())
        if match is None:
            break
        failed.append(match.group(1))
    return tuple(failed)


def parallel_jobs() -> int:
    """Lake's parallel jobs: the machine's processors, at most `MAX_PARALLEL_JOBS`."""
    return max(1, min(os.cpu_count() or 1, MAX_PARALLEL_JOBS))


def lake_build(directory: Path, sysroot: Path, cache: Path, library_prefixes: Sequence[str],
               targets: Sequence[str] = (), timeout: float = BUILD_TIMEOUT_SECONDS) -> tuple[str, ...]:
    """Build the given targets (default: the workspace's default targets); return the compiled modules or
    raise `CompileError`."""
    result = run_process([str(sysroot / "bin/lake"), "build", *targets, "--no-ansi", "--keep-toolchain"],
                         write_root=directory,
                         environment={"LAKE_CACHE_DIR": str(cache), "LEAN_NUM_THREADS": str(parallel_jobs())},
                         timeout=timeout)
    output = result.stdout + result.stderr
    if result.returncode:
        failed = failed_targets(output) or ("(workspace)",)
        raise CompileError(", ".join(failed), "compile", output.strip())
    return compiled_modules(output, library_prefixes)
