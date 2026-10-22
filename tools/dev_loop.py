"""`python3 -m tools.dev_loop`: the local incremental build loop of model work (ADR 0020).

`build [TARGET...]` runs `lake build` in the Lean packages under `packages/`, so that an edit
compiles only the modules that it changes. `verdict [CORPUS...]` builds the two programs of
the conformance subject, copies them into the runtime root `build/dev/runtime/`, and runs the
judge over the claimed corpora with them. Both need the shell of `shell.nix`, which `.envrc`
loads: it has the pinned toolchain and the Nix build's parser library. A local result is
feedback while editing, not evidence; the Nix checks before each commit decide.
"""

from collections.abc import Mapping, Sequence
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from conformance.predict import RUNNER
from conformance.sql_text import PROGRAM
from judge.cells import Json

ROOT = Path(__file__).resolve().parents[1]
PACKAGE_TARGETS: dict[str, tuple[str, ...]] = {
    "belay-sqlite-model": ("Belay.Sqlite.Model", "Belay.Sqlite.Model.Codec"),
    "belay-sqlite-text": ("BelaySqliteText", "BelaySqliteText:shared", "parserShim:shared",
                          "belay-sqlite-translate"),
    "verifier-conformance": ("conformance-runner",),
    "belay": ("Belay", "Belay:shared"),
}
"""The Lean packages under `packages/` and the targets that model work can break, in build order."""
SUBJECT_PROGRAMS: dict[str, tuple[str, str]] = {
    PROGRAM: ("belay-sqlite-text", "belay-sqlite-translate"),
    RUNNER: ("verifier-conformance", "conformance-runner"),
}
"""Each program of a conformance runtime root, by its path there, and its package and target."""
LAKE_TIMEOUT_SECONDS = 1800
"""One `lake build` of a package; a clean build of the model took about one minute."""
JUDGE_TIMEOUT_SECONDS = 3600
"""One local judge run over all claimed corpora took about one minute."""


class DevLoopError(Exception):
    """A problem that stops the loop before it builds, with what to do next."""


def resolved_targets(arguments: Sequence[str]) -> dict[str, tuple[str, ...]]:
    """The targets to build for each package, in build order.

    No arguments mean all targets of `PACKAGE_TARGETS`. `PACKAGE` means that package's targets;
    `PACKAGE/TARGET` means one target, which need not be in the table."""
    if not arguments:
        return dict(PACKAGE_TARGETS)
    chosen: dict[str, list[str]] = {}
    for argument in arguments:
        package, _, target = argument.partition("/")
        if package not in PACKAGE_TARGETS:
            raise DevLoopError(f"unknown package {package!r} in {argument!r}. Name one of "
                               f"{', '.join(PACKAGE_TARGETS)}, as PACKAGE or PACKAGE/TARGET.")
        names = chosen.setdefault(package, [])
        names.extend(name for name in ((target,) if target else PACKAGE_TARGETS[package]) if name not in names)
    return {package: tuple(chosen[package]) for package in PACKAGE_TARGETS if package in chosen}


def shell_problem(environment: Mapping[str, str], linux: bool) -> str | None:
    """Why the current environment is not the shell of `shell.nix`, or None when it is."""
    missing = [name for name in ("BELAY_PARSER_LIBRARY", *(("LEAN_CC",) if linux else ()))
               if not environment.get(name)]
    if not missing:
        return None
    return (f"{' and '.join(missing)} {'is' if len(missing) == 1 else 'are'} not set: this is not the "
            f"shell of shell.nix. Change into "
            f"{ROOT} so that direnv loads it, or, if direnv reports that .envrc is blocked, ask "
            f"the owner to run `direnv allow` there.")


def stale_links(root: Path) -> list[Path]:
    """The `.lake/build` links into the Nix store that `just build` made before ADR 0020.

    Lake cannot write through them: the outputs in the store are read-only."""
    return [path for path in sorted((root / "packages").glob("*/.lake/build")) if path.is_symlink()]


def reduced_claims(document: Mapping[str, Json], corpora: Sequence[str]) -> dict[str, Json]:
    """The claims file with only the named corpora, whose claims it copies unchanged."""
    claimed = document["corpora"]
    assert isinstance(claimed, dict)
    unknown = [corpus for corpus in corpora if corpus not in claimed]
    if unknown:
        raise DevLoopError(f"no claim for {', '.join(unknown)} in judge/claims.json. Name claimed "
                           f"corpora, for example {', '.join(sorted(claimed)[:3])}.")
    return {**document, "corpora": {corpus: claimed[corpus] for corpus in sorted(set(corpora))}}


def make_runtime_root(runtime: Path, packages: Path) -> None:
    """Copy the locally built programs of `SUBJECT_PROGRAMS` to their paths in the runtime root."""
    for relative, (package, target) in SUBJECT_PROGRAMS.items():
        source = packages / package / ".lake/build/bin" / target
        destination = runtime / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.unlink(missing_ok=True)
        shutil.copy2(source, destination)


def check_ready(root: Path, environment: Mapping[str, str], linux: bool) -> None:
    """Stop before a build that cannot work, and say what to do."""
    problem = shell_problem(environment, linux)
    if problem:
        raise DevLoopError(problem)
    links = stale_links(root)
    if links:
        raise DevLoopError(f"{', '.join(map(str, links))}: a link into the read-only Nix store, which "
                           f"an older `just build` made. Delete it: rm {' '.join(map(str, links))}")


def build(root: Path, targets: Mapping[str, Sequence[str]]) -> int:
    """Run `lake build` for each package's targets in turn; stop at the first failure."""
    for package, names in targets.items():
        directory = root / "packages" / package
        print(f"dev-build: lake build {' '.join(names)} in {directory}", flush=True)
        result = subprocess.run(["lake", "build", *names], cwd=directory, timeout=LAKE_TIMEOUT_SECONDS,
                                check=False)
        if result.returncode:
            print(f"dev-build: lake build failed in {directory} with exit code {result.returncode}. Read "
                  f"Lake's errors above, fix the named files, and run `just dev-build` again.", file=sys.stderr)
            return result.returncode
    return 0


def verdict(root: Path, corpora: Sequence[str]) -> int:
    """Build the subject's programs, make the runtime root, and run the judge with it."""
    targets = resolved_targets([f"{package}/{target}" for package, target in SUBJECT_PROGRAMS.values()])
    claims = root / "judge/claims.json"
    if corpora:
        reduced = reduced_claims(json.loads(claims.read_text(encoding="utf-8")), corpora)
        claims = root / "build/dev/claims.json"
        claims.parent.mkdir(parents=True, exist_ok=True)
        claims.write_text(json.dumps(reduced, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    built = build(root, targets)
    if built:
        return built
    runtime = root / "build/dev/runtime"
    make_runtime_root(runtime, root / "packages")
    report = root / "build/dev/report.json"
    result = subprocess.run([sys.executable, "-m", "judge", "run", "--root", ".", "--claims", str(claims),
                             "--report", str(report), "--", sys.executable, "-m", "conformance.predict",
                             "--runtime", str(runtime)], cwd=root, timeout=JUDGE_TIMEOUT_SECONDS, check=False)
    print(f"dev-verdict: the judge exited with {result.returncode}; the report is {report}. This local "
          f"result is not evidence: run `just verdict` before you cite a verdict.", file=sys.stderr)
    return result.returncode


def main(arguments: Sequence[str]) -> int:
    """Run `build` or `verdict` with the remaining arguments."""
    if not arguments or arguments[0] not in ("build", "verdict"):
        print("usage: python3 -m tools.dev_loop build [PACKAGE | PACKAGE/TARGET]... | verdict [CORPUS]...",
              file=sys.stderr)
        return 2
    try:
        check_ready(ROOT, os.environ, sys.platform.startswith("linux"))
        if arguments[0] == "build":
            return build(ROOT, resolved_targets(arguments[1:]))
        return verdict(ROOT, arguments[1:])
    except DevLoopError as error:
        print(f"dev-{arguments[0]}: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
