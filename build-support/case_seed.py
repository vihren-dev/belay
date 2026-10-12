"""Fill a Lake artifact cache with one case's outputs: the Nix seed of ADR 0010 section 8.

Usage: python3 case_seed.py RUNTIME CASE_FOLDER CASE_ROOT CACHE

Runs the installed `prepare` and `verify-bundle` on the case with `--cache CACHE`, so
the cache holds the outputs of both the proofs project and `verify-bundle`'s own
workspace. Test targets copy the seeds of their cases into one writable cache, and
then a test that runs a case unchanged compiles nothing. The case's `[test]` status
must come out, so a broken case fails the seed instead of a later test.
"""

import json
from pathlib import Path
import subprocess
import sys

TIMEOUT_SECONDS = 600
"""Deadline for one command; the Atuin case prepares in about 8 s from an empty cache."""


def main(runtime: Path, case: Path, root: Path, cache: Path) -> None:
    """Prepare and verify the case into `cache`; stop with the command's report on a wrong status."""
    sys.path.insert(0, str(runtime))
    from migration_check.project_config import load

    config = load(case / "belay.toml", root)
    launcher, bundle = str(runtime / "bin/migration-check"), case / "seed.bundle"
    commands = (["prepare", *config.contract_arguments(), "--project", str(config.proofs), "--output", str(bundle)],
                ["verify-bundle", *config.contract_arguments(), "--bundle", str(bundle)])
    for command, expected in zip(commands, ("PREPARED", config.test_status), strict=True):
        result = subprocess.run([launcher, *command, "--cache", str(cache), "--format", "json"], capture_output=True,
                                text=True, timeout=TIMEOUT_SECONDS, check=False)
        report = json.loads(result.stdout)
        if report.get("status") != expected:
            raise SystemExit(f"{case}: {command[0]} gave {report}, expected {expected}; correct the case, "
                             "then build the seed again")


if __name__ == "__main__":
    main(*(Path(argument).resolve() for argument in sys.argv[1:5]))
