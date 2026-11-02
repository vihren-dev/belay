"""Observe the local Nix daemon through its documented commands, outside builders."""

import argparse
import json
from pathlib import Path
import uuid

from probe_support import run, write_json


def measure(root: Path, output: Path) -> None:
    """Compare build/reuse, input changes and failure evidence without private events."""
    output.mkdir(parents=True, exist_ok=False)
    seed = str(uuid.uuid4())
    fixture = str(root / "experiments/observability/nix_fixture.nix")

    def instantiate(label: str, *arguments: str) -> str:
        """Record the input-addressed derivation for one isolated fixture variant."""
        result = run(output, label, ["nix-instantiate", fixture, "--argstr", "seed", seed, *arguments], cwd=root)
        return result.stdout.strip()

    base = instantiate("base-identity")
    same = instantiate("irrelevant-identity", "--argstr", "irrelevant", "changed")
    changed = instantiate("relevant-identity", "--argstr", "relevant", "changed")
    assert base == same and base != changed
    build_results: dict[str, object] = {}
    original_events = ""
    for label, derivation in (("fresh", base), ("reuse", base), ("changed", changed)):
        shown = run(output, label + "-derivation", ["nix", "derivation", "show", derivation], cwd=root)
        json.loads(shown.stdout)
        built = run(output, label, ["nix", "build", "--json", "--no-link", derivation + "^*"], cwd=root)
        result = json.loads(built.stdout)
        assert len(result) == 1
        path = Path(result[0]["outputs"]["out"])
        event_text = (path / "events.jsonl").read_text()
        if label == "fresh":
            original_events = event_text
        if label == "reuse":
            assert event_text == original_events
        if label == "changed":
            assert event_text != original_events
        build_results[label] = result
        (output / f"{label}-events.jsonl").write_text(event_text)
    failures: dict[str, object] = {}
    for outcome in ("fail", "abrupt"):
        derivation = instantiate(outcome + "-identity", "--argstr", "outcome", outcome)
        built = run(output, outcome + "-build", ["nix", "build", "--json", "--no-link", derivation + "^*"],
                    cwd=root, expected=None)
        assert built.returncode != 0
        paths = run(output, outcome + "-outputs", ["nix-store", "-q", "--outputs", derivation], cwd=root)
        output_paths = paths.stdout.splitlines()
        valid = run(output, outcome + "-validity", ["nix-store", "--check-validity", *output_paths],
                    cwd=root, expected=None)
        assert valid.returncode != 0
        log = run(output, outcome + "-log", ["nix", "log", derivation], cwd=root)
        records = [json.loads(line.removeprefix("BELAY_EVENT ")) for line in log.stdout.splitlines()
                   if line.startswith("BELAY_EVENT ")]
        assert any(record["kind"] == "test_start" for record in records)
        finished = any(record["kind"] == "session_finish" for record in records)
        assert finished == (outcome == "fail")
        failures[outcome] = {"build_exit": built.returncode, "log_events": len(records),
            "session_finished": finished, "valid_output": False,
            "leftover_output_exists": any(Path(path).exists() for path in output_paths)}
    graph = json.loads((output / "fresh-derivation.stdout").read_text())
    assert graph["version"] == 4, "This probe targets the installed Nix JSON schema"
    subject = next(iter(graph["derivations"].values()))["env"]["subjectInput"]
    dependency = run(output, "dependency-path", ["nix", "why-depends", "--derivation", base, subject],
                     cwd=root, expected=None)
    identity = run(output, "source", ["jj", "log", "-r", "@", "--no-graph", "-T",
        'commit_id ++ " " ++ change_id ++ "\\n"'], cwd=root).stdout.strip()
    version = run(output, "version", ["nix", "--version"], cwd=root).stdout.strip()
    write_json(output / "summary.json", {"scope": "local Nix daemon; not a CI execution",
        "version": version, "source_identity": identity, "seed": seed,
        "irrelevant_input_preserves_identity": True, "relevant_input_changes_identity": True,
        "cached_result_preserves_original_execution": True, "build_results": build_results,
        "failed_builds": failures, "why_depends_exit": dependency.returncode})


def main() -> None:
    """Require a fresh evidence directory so observations from runs cannot mix."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    measure(args.root.resolve(), args.output.resolve())


if __name__ == "__main__":
    main()
