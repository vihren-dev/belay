"""`python -m judge`: give the subject its inputs and check the development claims (ADR 0011).

Three modes:

- `inputs --out DIR`: write each claimed corpus's subject inputs to `DIR/CORPUS.jsonl`.
- `verdict --predictions DIR`: read `DIR/CORPUS.jsonl`, one prediction per input line in the
  same order, and check the claims.
- `run -- SUBJECT-COMMAND`: both, with the subject command reading inputs on standard input
  and writing predictions on standard output.

The verdict job uses the first two in separate Nix builds, so that the subject runs where the
recorded observations are not readable. Exit code 0: every claim holds; 1: a claim fails;
2: the judge could not run.
"""

import argparse
from collections.abc import Sequence
import json
from pathlib import Path
import subprocess
import sys

from judge.claims import Claim, claim_failures, counts, load_claims
from judge.compare import Verdict, case_verdict
from judge.cells import Json
from judge.records import corpus_records, subject_input

SUBJECT_TIMEOUT_SECONDS = 1800
"""The longest time the subject may take for one corpus in `run` mode."""


def records(root: Path, claim: Claim) -> list[dict[str, Json]]:
    """The records of one claimed corpus; case names must be unique."""
    loaded = list(corpus_records(root / claim.path))
    names = [record["name"] for record in loaded]
    if len(set(names)) != len(names):
        raise ValueError(f"{claim.corpus}: two records have the same name")
    return loaded


def input_lines(loaded: list[dict[str, Json]]) -> str:
    """The subject inputs of one corpus, one JSON line per record."""
    return "".join(json.dumps(subject_input(record), sort_keys=True) + "\n" for record in loaded)


def decoded(text: str, expected: int, source: str) -> list[Json]:
    """One prediction per line, exactly as many as there were inputs."""
    lines = [line for line in text.splitlines() if line.strip()]
    if len(lines) != expected:
        raise RuntimeError(f"{source} has {len(lines)} predictions for {expected} inputs; the subject must "
                           f"write exactly one prediction line per input line")
    return [json.loads(line) for line in lines]


def run_subject(subject: Sequence[str], loaded: list[dict[str, Json]]) -> list[Json]:
    """Run the subject once over all inputs of a corpus."""
    result = subprocess.run(list(subject), input=input_lines(loaded), capture_output=True, text=True,
                            timeout=SUBJECT_TIMEOUT_SECONDS, check=False)
    if result.returncode:
        raise RuntimeError(f"the subject exited with {result.returncode}: {result.stderr.strip()[-2000:]}")
    return decoded(result.stdout, len(loaded), f"the output of `{' '.join(subject)}`")


def check(claims: list[Claim], verdicts: dict[str, dict[str, Verdict]], report_path: Path | None) -> int:
    """Print the counts and every failure; write the full report if asked."""
    report = {corpus: {"counts": counts(found), "verdicts": {
        name: [verdict.name, verdict.position, verdict.detail] for name, verdict in sorted(found.items())}}
        for corpus, found in verdicts.items()}
    if report_path:
        report_path.write_text(json.dumps(report, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({corpus: entry["counts"] for corpus, entry in report.items()}, sort_keys=True))
    failures = [failure for claim in claims for failure in claim_failures(claim, verdicts[claim.corpus])]
    for failure in failures:
        print(f"judge: {failure}", file=sys.stderr)
    return 1 if failures else 0


def main(arguments: Sequence[str]) -> int:
    """Run one mode of the judge."""
    parser = argparse.ArgumentParser(prog="python -m judge", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=("inputs", "verdict", "run"))
    parser.add_argument("--root", type=Path, required=True, help="directory that holds the corpora")
    parser.add_argument("--claims", type=Path, required=True)
    parser.add_argument("--out", type=Path, help="inputs mode: directory for the subject inputs")
    parser.add_argument("--predictions", type=Path, help="verdict mode: directory of the subject's predictions")
    parser.add_argument("--report", type=Path, help="write the full verdict report here")
    split = list(arguments).index("--") if "--" in arguments else len(arguments)
    options, subject = parser.parse_args(list(arguments)[:split]), list(arguments)[split + 1:]
    if options.mode == "run" and not subject:
        parser.error("run mode needs the subject command after --")
    try:
        claims = load_claims(options.claims)
        if options.mode == "inputs":
            options.out.mkdir(parents=True, exist_ok=True)
            for claim in claims:
                (options.out / f"{claim.corpus}.jsonl").write_text(input_lines(records(options.root, claim)))
            return 0
        verdicts = {}
        for claim in claims:
            loaded = records(options.root, claim)
            if options.mode == "run":
                predicted = run_subject(subject, loaded)
            else:
                path = options.predictions / f"{claim.corpus}.jsonl"
                predicted = decoded(path.read_text(encoding="utf-8"), len(loaded), str(path))
            verdicts[claim.corpus] = {record["name"]: case_verdict(record, prediction)
                                      for record, prediction in zip(loaded, predicted)}
    except (OSError, ValueError, KeyError, TypeError, AttributeError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"judge: cannot check the claims: {error}. Check the --root, --claims, --out or --predictions "
              f"paths and the subject command.", file=sys.stderr)
        return 2
    return check(claims, verdicts, options.report)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
