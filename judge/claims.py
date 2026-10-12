"""Development claims: which verdicts each frozen corpus must have.

A claim names a corpus, the cases that must agree, and the verdicts that no case may have.
The agreement floor is necessary: without it, a subject that declares every case out of its
scope would pass. `judge/claims.json` holds the claims; ADR 0011 describes how they change.
"""

from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path

from judge.compare import VERDICTS, Verdict


@dataclass(frozen=True)
class Claim:
    """The required verdicts of one frozen corpus."""

    corpus: str
    path: str
    must_agree: frozenset[str]
    forbidden: frozenset[str]


def load_claims(path: Path) -> list[Claim]:
    """Read and check the claims file."""
    document = json.loads(path.read_text(encoding="utf-8"))
    claims = []
    for corpus, entry in sorted(document["corpora"].items()):
        forbidden = frozenset(entry["forbidden"])
        if not forbidden <= set(VERDICTS) - {"AGREE"}:
            raise ValueError(f"{path}: {corpus}: unknown or impossible forbidden verdicts {sorted(forbidden)}")
        claims.append(Claim(corpus, entry["path"], frozenset(entry["mustAgree"]), forbidden))
    return claims


def claim_failures(claim: Claim, verdicts: dict[str, Verdict]) -> list[str]:
    """Why the verdicts of one corpus break its claim; empty when the claim holds."""
    failures = [f"{claim.corpus}: case {name} is {verdicts[name].name}, the claim requires AGREE"
                f"{': ' + verdicts[name].detail if verdicts[name].detail else ''}"
                for name in sorted(claim.must_agree) if name in verdicts and verdicts[name].name != "AGREE"]
    failures += [f"{claim.corpus}: case {name} is not in the corpus" for name in sorted(claim.must_agree - set(verdicts))]
    failures += [f"{claim.corpus}: case {name} is {verdict.name}, which the claim forbids"
                 f"{' at statement ' + str(verdict.position) if verdict.position is not None else ''}: {verdict.detail}"
                 for name, verdict in sorted(verdicts.items()) if verdict.name in claim.forbidden]
    return failures


def counts(verdicts: dict[str, Verdict]) -> dict[str, int]:
    """The number of cases with each verdict."""
    return dict(sorted(Counter(verdict.name for verdict in verdicts.values()).items()))
