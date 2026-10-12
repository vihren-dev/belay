"""The judge of development claims (`judge/`, ADR 0011) against stand-in subjects.

A stand-in subject reads the recorded answers of a small corpus copied from corpus v1, so the
tests show what the judge does with an honest, a wrong, an evasive and a broken subject,
without the model. The real subject is checked by the verdict job.
"""

import gzip
import json
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
JUDGE_TIMEOUT_SECONDS = 60
"""One judge run over five small cases."""
CASES = 5
"""The number of corpus v1 records in the fixture corpus."""

SUBJECT = '''
import gzip, json, sys
records = {{}}
for line in gzip.open(sys.argv[1], "rt"):
    record = json.loads(line)
    records[record["name"]] = record
MODE = {mode!r}
for line in sys.stdin:
    given = json.loads(line)
    record = records[given["name"]]
    if MODE == "crash":
        sys.exit(3)
    if MODE == "unsupported":
        print(json.dumps({{"name": given["name"], "status": "unsupported", "reason": "stand-in"}}))
        continue
    steps, offset = [record["initial"]], 0
    for event in record["trace"]:
        steps.append({{**event, "start": offset}})
        offset += len(event["sql"].encode())
    if MODE == "wrong" and len(steps) > 1:
        steps[1] = {{**steps[1], "transactionOpen": not steps[1]["transactionOpen"]}}
    if MODE == "malformed":
        steps = []
    print(json.dumps({{"name": given["name"], "status": "predicted", "supported": True, "steps": steps}}))
'''


@pytest.fixture(scope="module")
def corpus(tmp_path_factory: pytest.TempPathFactory) -> Path:
    """A corpus of the first five corpus v1 records that have at least one executed statement."""
    root = tmp_path_factory.mktemp("judge")
    chosen = []
    with gzip.open(ROOT / "conformance/corpus-v1/cases.jsonl.gz", "rt") as stream:
        for line in stream:
            if json.loads(line)["trace"] and len(chosen) < CASES:
                chosen.append(line)
    (root / "corpus").mkdir()
    with gzip.open(root / "corpus/cases.jsonl.gz", "wt") as stream:
        stream.writelines(chosen)
    return root


def run_judge(root: Path, mode: str, must_agree: list[str] | None = None) -> subprocess.CompletedProcess[str]:
    """Run `python -m judge` with a stand-in subject and one claim over the fixture corpus."""
    names = [json.loads(line)["name"] for line in gzip.open(root / "corpus/cases.jsonl.gz", "rt")]
    claims = root / f"claims-{mode}.json"
    claims.write_text(json.dumps({"corpora": {"fixture": {
        "path": "corpus", "mustAgree": names if must_agree is None else must_agree,
        "forbidden": ["DISAGREE", "HARNESS_ERROR"]}}}))
    subject = root / f"subject-{mode}.py"
    subject.write_text(SUBJECT.format(mode=mode))
    return subprocess.run([sys.executable, "-m", "judge", "--root", str(root), "--claims", str(claims),
                           "--", sys.executable, "-I", str(subject), str(root / "corpus/cases.jsonl.gz")],
                          cwd=ROOT, capture_output=True, text=True, timeout=JUDGE_TIMEOUT_SECONDS, check=False)


@pytest.mark.integration
def test_honest_subject_meets_the_claim(corpus: Path) -> None:
    """Predicting exactly what SQLite recorded agrees on every case."""
    result = run_judge(corpus, "honest")
    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout) == {"fixture": {"AGREE": CASES}}


@pytest.mark.integration
def test_wrong_prediction_disagrees_at_its_statement(corpus: Path) -> None:
    """One wrong transaction state in the first statement is DISAGREE at statement 0."""
    result = run_judge(corpus, "wrong")
    assert result.returncode == 1
    assert json.loads(result.stdout) == {"fixture": {"DISAGREE": CASES}}
    assert "which the claim forbids at statement 0: observation differs" in result.stderr


@pytest.mark.integration
def test_unsupported_everything_fails_the_agreement_floor(corpus: Path) -> None:
    """A subject that declares every case out of scope breaks the agreement floor, though
    nothing disagrees; without a floor the same subject passes."""
    result = run_judge(corpus, "unsupported")
    assert result.returncode == 1 and "the claim requires AGREE" in result.stderr
    assert json.loads(result.stdout) == {"fixture": {"MODEL_UNSUPPORTED": CASES}}
    assert run_judge(corpus, "unsupported", must_agree=[]).returncode == 0


@pytest.mark.integration
def test_broken_subject_is_a_failure(corpus: Path) -> None:
    """A subject that crashes stops the judge (exit 2); malformed predictions are HARNESS_ERROR."""
    crashed = run_judge(corpus, "crash")
    assert crashed.returncode == 2 and "the subject exited with 3" in crashed.stderr
    malformed = run_judge(corpus, "malformed")
    assert malformed.returncode == 1
    assert json.loads(malformed.stdout) == {"fixture": {"HARNESS_ERROR": CASES}}
