"""Probe a small allowlisted run envelope and existing semantic metadata exports."""

from collections.abc import Mapping
import json
import os
from pathlib import Path
import sys

from probe_support import write_json

CI_KEYS = ("GITHUB_REPOSITORY", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_JOB",
           "GITHUB_SHA", "GITHUB_EVENT_NAME", "RUNNER_OS", "RUNNER_ARCH", "SQLITE_VERIFIER_SYSTEM")
"""Documented CI identities plus the existing project platform variable; no credentials."""


def context(environment: Mapping[str, str]) -> dict[str, object]:
    """Keep invocation identity outside cacheable derivations."""
    return {"origin": "github_actions" if environment.get("GITHUB_ACTIONS") == "true" else "local",
            "ci": {key: environment[key] for key in CI_KEYS if key in environment}}


def measure(root: Path, output: Path) -> None:
    """Check metadata extraction without treating fixture CI values as a real CI run."""
    output.mkdir()
    sample = {"GITHUB_ACTIONS": "true", "GITHUB_RUN_ID": "fixture-run",
              "GITHUB_RUN_ATTEMPT": "2", "GITHUB_JOB": "check", "GITHUB_SHA": "fixture-sha",
              "SQLITE_VERIFIER_SYSTEM": "x86_64-linux", "GITHUB_TOKEN": "must-not-export"}
    envelope = context(sample)
    assert "must-not-export" not in json.dumps(envelope)
    assert envelope["origin"] == "github_actions" and context({})["origin"] == "local"
    write_json(output / "ci-fixture.json", {"scope": "simulated CI environment", **envelope})
    write_json(output / "actual-environment.json", context(os.environ))
    sys.path.insert(0, str(root))
    from conformance.key_mutants import GUARDS, MUTANTS, TARGETS
    assert set(MUTANTS) == set(TARGETS) == set(GUARDS)
    mapping = [{"mutant": name, "targets": list(TARGETS[name]), "guard": GUARDS[name]}
               for name in sorted(MUTANTS)]
    write_json(output / "mutant-targets.json", mapping)
    fixtures = [json.loads(path.read_text()) for path in sorted((root / "conformance/cases").glob("*.json"))]
    requirements = [{"provenance": case["provenance"], "requirements": case["requirements"]} for case in fixtures]
    assert fixtures
    write_json(output / "requirement-links.json", requirements)
    write_json(output / "summary.json", {"ci_scope": "environment fixture only; no live CI job launched",
        "static_mutant_targets": len(mapping), "mutant_outcomes_measured": False,
        "case_files": len(fixtures), "cases_with_requirement_tags": sum(bool(case["requirements"]) for case in fixtures),
        "scope": "Five key mutant declarations and authored JSON fixtures; not the complete corpus."})
