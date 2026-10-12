"""`python -m judge`: run the subject on the frozen corpora and check the development claims.

The subject is a command that reads one input per line (JSON) on standard input and writes
one prediction per line on standard output, in the same order. The judge gives it only the
inputs of `judge.records.subject_input`. Exit code 0: every claim holds; 1: a claim fails;
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
from judge.records import corpus_records, subject_input

SUBJECT_TIMEOUT_SECONDS = 1800
"""The longest time the subject may take for one corpus."""


def predictions(subject: Sequence[str], inputs: list[dict[str, object]]) -> list[object]:
    """Run the subject once over all inputs of a corpus and decode its output lines."""
    stdin = "".join(json.dumps(item, sort_keys=True) + "\n" for item in inputs)
    result = subprocess.run(list(subject), input=stdin, capture_output=True, text=True,
                            timeout=SUBJECT_TIMEOUT_SECONDS, check=False)
    if result.returncode:
        raise RuntimeError(f"the subject exited with {result.returncode}: {result.stderr.strip()[-2000:]}")
    lines = [line for line in result.stdout.splitlines() if line.strip()]
    if len(lines) != len(inputs):
        raise RuntimeError(f"the subject `{' '.join(subject)}` wrote {len(lines)} predictions for "
                           f"{len(inputs)} inputs; it must write exactly one prediction line per input line")
    return [json.loads(line) for line in lines]


def corpus_verdicts(root: Path, claim: Claim, subject: Sequence[str]) -> dict[str, Verdict]:
    """The verdict of each case of one claimed corpus."""
    records = list(corpus_records(root / claim.path))
    names = [record["name"] for record in records]
    if len(set(names)) != len(names):
        raise ValueError(f"{claim.corpus}: two records have the same name")
    predicted = predictions(subject, [subject_input(record) for record in records])
    return {record["name"]: case_verdict(record, prediction) for record, prediction in zip(records, predicted)}


def main(arguments: Sequence[str]) -> int:
    """Check every claim; print a JSON report and one line per failure."""
    parser = argparse.ArgumentParser(prog="python -m judge", description=main.__doc__)
    parser.add_argument("--root", type=Path, required=True, help="directory that holds the corpora")
    parser.add_argument("--claims", type=Path, required=True)
    parser.add_argument("--report", type=Path, help="write the full report here")
    parser.add_argument("subject", nargs=argparse.REMAINDER, help="-- SUBJECT-COMMAND [ARGUMENTS]")
    options = parser.parse_args(arguments)
    subject = options.subject[1:] if options.subject[:1] == ["--"] else options.subject
    if not subject:
        parser.error("give the subject command after --")
    try:
        report, failures = {}, []
        for claim in load_claims(options.claims):
            verdicts = corpus_verdicts(options.root, claim, subject)
            report[claim.corpus] = {"counts": counts(verdicts), "verdicts": {
                name: [verdict.name, verdict.position, verdict.detail] for name, verdict in sorted(verdicts.items())}}
            failures += claim_failures(claim, verdicts)
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"judge: cannot check the claims: {error}", file=sys.stderr)
        return 2
    if options.report:
        options.report.write_text(json.dumps(report, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({corpus: entry["counts"] for corpus, entry in report.items()}, sort_keys=True))
    for failure in failures:
        print(f"judge: {failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
