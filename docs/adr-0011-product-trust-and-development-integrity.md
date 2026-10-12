# ADR 0011: Product trust and development integrity

Date: 2026-10-12. Status: PROPOSED.
Audience: designers and reviewers.
Related: [ADR 0003](adr-0003-agent-proof-preparation.md),
[ADR 0005](adr-0005-conformance-corpus-scale.md), [kernel gate](kernel-gate.md),
[review checklist](review-checklist.md), [CI](ci.md), `.github/CODEOWNERS`.

## Context

Agents write most of the code in this repository. An agent that has a task
such as "make the model agree with SQLite on corpus v5" can also change the
corpus, the expected outputs, or the tests, so that the task appears done.
The repository has many checks against such changes, but they mix two
different questions, and the last defense is not enforced.

**Two kinds of trust are mixed.**

- Product trust: a user of the verifier must be able to trust a "verified"
  result, even when an untrusted agent wrote the proof, the bundle or the SQL.
  The verifier itself gives this guarantee: kernel replay against the trusted
  library, the axiom policy and the protected declarations (ADR 0003,
  `docs/kernel-gate.md`). The kernel and bundle attack tests check it.
- Development integrity: the owner must be able to trust that the agents that
  develop the verifier measured their work honestly, for example that the
  model agrees with SQLite on corpus v5 because the model is correct, and not
  because the corpus changed.

Review condition R8 ("Trust-relevant change") uses a development-process tool,
a review finding, for product-trust code. Of its 21 findings up to
2026-10-11, 16 were deferred with the reason "owner review required". The
review process cannot close such a finding.

**Many checks only make a change harder.** Pins, denominator checks, mutation
checks and native replay are in the same repository that the agent changes.
A check whose reference value is in an unprotected file does not stop a
determined agent: the agent changes the file and the reference in one commit.
For example, `conformance/pinned-corpora.json` pins the digest of each frozen
corpus, but an agent can change a corpus and its pin together.

**The judge is large and unprotected.** The code that decides AGREE or
DISAGREE for a frozen corpus starts at `conformance/replay_tiers.py`, which
imports 45 of the 79 modules in `conformance/`. The verdict function
`classifyCase` is in `VerifierConformance/Case.lean`. No owner approval is
needed to change any of them.

**Owner approval is not enforced.** On 2026-10-12, the `main` ruleset
(23934665) had `require_code_owner_review: false` and
`required_approving_review_count: 0`. The first line of `.github/CODEOWNERS`
says that the ruleset requires code-owner approvals; it does not.
`CODEOWNERS` also does not cover `conformance/`, `tests/`,
`packages/belay-sqlite/`, `belay/`, `GateCore.lean`, `GatePaths.lean`,
`BundleChecker.lean` or `ProofExporter.lean`. Agents open pull requests as
the GitHub App `vihren-agents`, so an owner approval is a second, independent
party.

## Decision

### 1. Keep product trust and development integrity apart

| | Product trust | Development integrity |
| --- | --- | --- |
| Question | Can a user trust a verified result? | Did development measure its work honestly? |
| Untrusted party | The producer of proofs, bundles and SQL | The agents that develop the verifier |
| Mechanism | The verifier: kernel replay, trusted library, axiom policy | The protected set and owner approval |
| Tests | External behavior; they run in every CI scope | The checks of the judge; they run when the protected set changes |
| Documents | Product documents, ADR 0003, `kernel-gate.md` | This ADR |

A product-trust mechanism is a product feature. It is designed, documented and
tested as such, and it does not depend on how the code was developed. A
development-integrity mechanism protects the owner's view of the work. It is
not part of the product and is not shipped.

### 2. Make tampering impossible with a small protected set

A change to a protected file needs the owner's approval before it can merge.
The protected set is small, so that the owner can review each change to it.
It contains the complete path from each reference to the CI verdict, and
nothing else:

- **Reference data identity.** Digests of the frozen corpora
  (`conformance/pinned-corpora.json`), not the corpora: a pin protects the
  bytes that it names.
- **Oracle.** The native SQLite build that produces the expected outputs:
  `nix/sqlite.nix` and `nix/flake.lock`.
- **Judge.** The code that turns the subject's outputs into a verdict, and the
  acceptance threshold of each claim (for example, which cases of corpus v5
  must agree). The judge is small and self-contained. It imports only
  protected files and the standard library, and it calls the subject only
  through a fixed interface. The subject cannot define or change its own
  verdict.
- **CI path.** The workflow and the commands that run the judge, the list of
  required checks, and `.github/CODEOWNERS`. A pull request runs the workflow
  from its own branch, so the workflow is part of the judge path.

The protected set does not contain instructions or advisory processes, such as
`AGENTS.md`, the review checklist or the review log. A change to them cannot
make a verdict pass.

### 3. Integrity checks are anchored or they are not integrity checks

A check that claims to prevent tampering compares against a file in the
protected set. A check whose reference value an unprotected change can also
change is not a tampering defense. It stays only as an ordinary test, if it
finds honest mistakes (an accidental edit, a damaged file) that are worth its
cost. Code whose only purpose is to make tampering harder is removed.

The review checklist gets this condition, and R8 is removed (see 5).

### 4. Enforcement

- The `main` ruleset requires a code-owner review and at least one approval.
- Agents use an identity without bypass, admin or merge rights. Only the owner
  merges.
- `.github/CODEOWNERS` has two labeled sections: the development protected set
  (2) and the product trust base (5). Its first line describes the actual
  ruleset.

### 5. Product trust base

Changes to the code that gives the product guarantee also need the owner's
review, because the guarantee depends on that code. This is a product reason,
not a defense against agents. The product trust base starts as the files in
the scope of review condition R8, plus the import-path check that its
findings covered outside that scope: the verification target
(`SqliteVerifier/Contract.lean`), the kernel gates (`GatePaths.lean`,
`GateCore.lean`, `ProofChecker.lean`, `BundleChecker.lean`), the export path,
`packages/belay-sqlite/Belay/Sqlite/Codec.lean`, and the approval, baseline and
import-path checks in `migration_check/`. With enforced code-owner review on
this set, review condition R8 has no remaining purpose and is removed.

## Consequences

- The owner reviews every change to the protected set and to the product trust
  base. Changes to other files, including the corpora, the model and most
  tests, need no owner approval, because they cannot change a verdict without
  a change in the protected set.
- The current judge must be extracted into a small module that imports no
  unprotected code. Until then, the judge path includes the 45 modules that
  `replay_tiers.py` imports, and the protected set is not small.
- Existing integrity checks are reviewed against decision 3. Checks without a
  protected anchor are removed or kept as ordinary tests; no check is kept as
  a tampering defense without an anchor.
- A task that changes a claim, such as a new corpus or a new threshold, has
  two pull requests: the protected change, which the owner approves, and the
  work, which does not touch the protected set.
- Product-trust tests are external-behavior tests and run in every CI scope.
  Judge checks run when the protected set changes.

## Alternatives considered

- **More in-repository checks** (stricter pins, more denominators, test-count
  checks). Rejected: each check lives where the agent writes, so an agent can
  change it together with what it checks. Each one adds maintenance without a
  guarantee.
- **Protect all of `conformance/` and `tests/`.** Rejected: the set is too large
  for the owner to review each change, so approvals become a formality.
- **Keep R8 as a review finding.** Rejected: a finding is advisory, and the
  review process cannot close "owner review required".
- **Store references outside the repository** (a signed manifest or a second
  repository). Not needed now: an enforced code-owner review on a small set
  gives the same guarantee with less machinery. Reconsider if the owner cannot
  review the protected set in time.

## Open points

- The exact files of the extracted judge, and how a claim states its threshold.
- Whether the oracle pin (`nix/flake.lock`) changes often enough for its
  reviews to become a burden.
