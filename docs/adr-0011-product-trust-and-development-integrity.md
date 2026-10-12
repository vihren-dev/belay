# ADR 0011: Product trust and development integrity

Date: 2026-10-12. Status: ACCEPTED on 2026-10-12 (PR #90).
Implementation: [task](../plans/20261012-development-integrity.task.md).
Audience: designers and reviewers.
Related: [ADR 0003](adr-0003-agent-proof-preparation.md),
[ADR 0005](adr-0005-conformance-corpus-scale.md), [kernel gate](kernel-gate.md),
[review checklist](review-checklist.md), [CI](ci.md), `.github/CODEOWNERS`.

## Overview

This section gives the model of the decision. The sections after it give the
evidence and the details.

The owner approves a **judge** once. A **lock** makes each later change to the
judge visible, and each such change needs the owner's approval. A CI job that
pull-request code cannot reach runs the locked judge on the agents' work, and
nothing merges unless the judge passes it.

### Entities

| Entity | Meaning | Example | Who changes it |
| --- | --- | --- | --- |
| Owner | The only party trusted to approve | the product owner | not applicable |
| Agent | Does the work; not trusted to grade it | Claude Code or Codex, as `vihren-agents` | not applicable |
| Subject | The work that is graded | the SQLite model | an agent, without approval |
| Claim | A statement that the owner wants to be true | "the model agrees with SQLite on corpus v5" | the owner |
| Judge | All that decides whether a claim is true: reference data, the oracle that produced it, comparison code, threshold | corpus v5, the native SQLite build, the verdict code, "all v5 cases agree" | an agent proposes; the owner approves |
| Lock | A fingerprint of the judge in one small file | `nix/judge.lock.json` | the owner approves each change |
| Gate | The files that enforce these rules | the Nix file that checks the lock, `.github/workflows/`, `.github/CODEOWNERS`, and the ruleset | the owner approves each change |
| Verdict | The result of the locked judge on the subject | the required check "verdict" | nobody; it is computed |

### Relationships

```
            approves                      approves
  Owner ───────────────► Lock ◄──────── Gate files
                           │ fingerprints       │ enforce
                           ▼                    ▼
  Claim ───defines───►  Judge ───grades───► Subject ◄─── changes ─── Agent
                           │                    │
                           └─────► Verdict ◄────┘
                                      │ required for
                                      ▼
                               merge into main (the owner merges)
```

- The judge grades the subject. The subject never grades itself: the judge
  gives it inputs and reads its outputs, as the product's checker treats a
  proof as data.
- The lock is computed from all inputs of the judge. A change to any input
  changes the lock, so no list of judge files is necessary.
- The gate makes the owner's approval necessary for the lock and the gate
  files, and makes a passing verdict necessary for a merge.

### Workflows

**Set or change a claim** (rare; the owner reviews):

1. An agent prepares a change to the judge, for example a new corpus or a new
   threshold.
2. The lock changes. The lock file needs a code-owner review, so the pull
   request cannot merge without the owner.
3. The owner reviews the change behind the lock (corpus, threshold, comparison
   code), approves and merges. From then on, that judge grades all work.

**Do the work** (frequent; no owner review):

1. An agent changes the subject and opens a pull request. The judge and the
   lock do not change.
2. The verdict job starts on a clean runner and runs only gate steps. It
   compares the judge's fingerprint with the lock, runs the locked judge on the
   subject in the Nix sandbox, and reports the verdict.
3. The ordinary test job runs separately and makes no integrity claim.
4. With a passing verdict, the pull request can merge without an owner review.

### Attempts and what stops them

| An agent tries to | What stops it |
| --- | --- |
| Change corpus v5 so that the outputs agree | The lock changes, and the lock needs the owner |
| Change the lock in the same pull request | The lock file needs a code-owner review |
| Weaken the comparison code or a module that it imports | The module is an input of the judge, so the lock changes |
| Change the SQLite build that produced the expected outputs | The build is an input of the judge, so the lock changes |
| Change the Nix store or the result files from a test | Test code does not run in the verdict job |
| Put changed content into the CI cache | Pull requests cannot save the cache; only `main` and scheduled runs can |
| Add a workflow that reports a passing "verdict" | `.github/workflows/` needs a code-owner review |
| Change `.github/CODEOWNERS` or the lock check | Both need a code-owner review |
| Merge without these checks | The ruleset requires the verdict and the owner's approval; agents cannot merge or bypass |

A passing verdict means: the subject passes the judge that the owner
approved. It does not mean that the judge is good; that depends on the owner's
review when the claim is set.

Product trust is a different chain: an untrusted author gives a proof bundle
to the verifier, which replays it in the kernel against the trusted library.
The verifier rejects a forged proof whoever developed the verifier. Decision 1
keeps the two chains apart.

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

**Many checks only make a change harder.** Pins, denominator checks, digest
and receipt bindings, and the report validators in `reports/` are in the same
repository that the agent changes. A check whose reference value is in an
unprotected file does not stop a determined agent: the agent changes the file
and the reference in one commit. For example, `conformance/pinned-corpora.json`
pins the digest of each frozen corpus, but an agent can change a corpus and
its pin together. About 52 of the 572 test functions and 15 report validators
are of this kind. The validators in `reports/` alone received 46 of the 250
review findings up to 2026-10-11.

**The judge is large and unprotected.** The code that decides AGREE or
DISAGREE for a frozen corpus starts at `conformance/replay_tiers.py`, which
imports 45 of the 79 modules in `conformance/`. The verdict function
`classifyCase` is in `VerifierConformance/Case.lean`. No owner approval is
needed to change any of them.

**Owner approval is not enforced.** On 2026-10-12, the `main` ruleset
(23934665) had `require_code_owner_review: false` and
`required_approving_review_count: 0`. The first line of `.github/CODEOWNERS`
says that the ruleset requires code-owner approvals; it does not. Agents open
pull requests as the GitHub App `vihren-agents`, so an owner approval is a
second, independent party.

**Where pull-request code can reach the judge.** Measured on 2026-10-12:

| Place | Can pull-request code change the judge or its result? | Reason |
| --- | --- | --- |
| Developer machine | No | The Nix store belongs to root; agent accounts are not Nix trusted users; `require-sigs` and the build sandbox are on. A local result also decides nothing. |
| CI Nix cache | No | Only scheduled runs and pushes to `main` save it (`.github/workflows/ci.yml`). |
| The current CI job | Yes | One job runs the host tests, which are pull-request code, as a user with `sudo`, before the conformance suites. That code can change the Nix store or the result files. |

A fixed-output source pin, `builtins.path { sha256 = ...; }`, is not a check:
when the store already has the path, Nix uses it and does not read the
changed files.

**Review load.** Of the 48 pull requests merged from 2026-09-28 to
2026-10-12, these would have needed an owner review:

| Protected set | Pull requests |
| --- | --- |
| Corpora, tests, model and judge sources | 41 (85%) |
| The current `CODEOWNERS`, if enforced | 30 (62%) |
| The protected set of this ADR, with the product trust base | 19 (40%) |
| The same, without `.github/workflows/` | 10 (21%) |

Workflow changes cause most of the load: 12 of the 48 pull requests changed
`.github/workflows/`, many of them during CI-time work.

## Decision

### 1. Keep product trust and development integrity apart

| | Product trust | Development integrity |
| --- | --- | --- |
| Question | Can a user trust a verified result? | Did development measure its work honestly? |
| Untrusted party | The producer of proofs, bundles and SQL | The agents that develop the verifier |
| Mechanism | The verifier: kernel replay, trusted library, axiom policy | The judge lock, the verdict job and owner approval |
| Tests | External behavior; they run in every CI scope | The verdict; it runs when the subject or the lock changes |
| Documents | Product documents, ADR 0003, `kernel-gate.md` | This ADR |

A product-trust mechanism is a product feature. It is designed, documented and
tested as such, and it does not depend on how the code was developed. A
development-integrity mechanism protects the owner's view of the work. It is
not part of the product and is not shipped.

### 2. Lock the judge with Nix

The judge is a Nix derivation: the code that turns the subject's outputs into
a verdict, the acceptance threshold of each claim, the frozen corpora, and the
native SQLite build that produced the expected outputs. A lock file
(`nix/judge.lock.json`) records the judge's derivation path for each system.
Nix computes the derivation path from all inputs: sources, `nix/flake.lock`,
`nix/sqlite.nix` and the build commands. A change to any of them changes the
path, so the lock covers the judge's dependencies without a list of files.

A small Nix file reads the lock, compares it with the derivation path that it
evaluates, and stops with an error that names the changed part when they
differ. Sources enter the store as content-derived paths, not as fixed-output
paths with a declared hash, so that the comparison does not depend on what the
store already holds. The same file defines the verdict: it runs the locked
judge on the subject, for example the model, in the Nix sandbox.

The judge calls the subject only through a fixed interface. The subject cannot
define or change its own verdict.

### 3. Run the verdict in its own CI job

The verdict runs in a separate CI job that is a required check. The job runs
only protected steps: it evaluates the lock and builds the verdict in the Nix
sandbox. No pull-request code runs on the host of that job. Its Nix store
comes from Nix's own substitution and builds, or from a cache that only `main`
saves. The current CI job stays for ordinary tests, which make no integrity
claim.

### 4. Protect a small set of files and enforce it

A change to these files needs the owner's approval before it can merge:

- `nix/judge.lock.json`: the judge lock.
- The Nix file that enforces the lock and defines the verdict.
- `.github/workflows/`: a pull request runs workflows from its own branch, and
  a new workflow could report a check with the verdict's name.
- `.github/CODEOWNERS`.

Enforcement:

- The `main` ruleset requires a code-owner review and at least one approval.
- Agents use an identity without bypass, admin or merge rights. Only the owner
  merges.
- The first line of `.github/CODEOWNERS` describes the actual ruleset.

The protected set does not contain instructions or advisory processes, such as
`AGENTS.md`, the review checklist or the review log. A change to them cannot
make a verdict pass.

**Budget.** If more than about one in five pull requests needs an owner review
under decisions 4 and 6, the protected set is too large and this ADR is
reconsidered.

### 5. Integrity checks are anchored or they are not integrity checks

A check that claims to prevent tampering compares against a protected value: a
file of decision 4 or a part of the judge lock. A check whose reference value
an unprotected change can also change is not a tampering defense. It stays
only as an ordinary test, if it finds honest mistakes (an accidental edit, a
damaged file) that are worth its cost. Code whose only purpose is to make
tampering harder is removed, but only after decisions 2 to 4 are in force.

The review checklist gets this condition.

### 6. Product trust base

Changes to the code that gives the product guarantee also need the owner's
review, because the guarantee depends on that code. This is a product reason,
not a defense against agents. The product trust base starts as the files in
the scope of review condition R8, plus the import-path check that its findings
covered outside that scope: the verification target
(`SqliteVerifier/Contract.lean`), the kernel gates (`GatePaths.lean`,
`GateCore.lean`, `ProofChecker.lean`, `BundleChecker.lean`),
`packages/belay-sqlite/Belay/Sqlite/Codec.lean`, and `prepare.py`, `bundle.py`,
`baseline.py` and `import_path.py` in `migration_check/`. `.github/CODEOWNERS`
lists it in its own section. With enforced code-owner review on this set,
review condition R8 has no remaining purpose and is removed.

## Consequences

- Changes to the corpora, the model and most tests need no owner approval:
  they cannot change a verdict without a change to the lock.
- A change to the judge, a new corpus, a new threshold or a `nix/flake.lock`
  update changes the lock, and the owner reviews the change behind it. The
  lock diff only shows that a review is due; the source diff shows what to
  approve.
- A task that changes a claim has two pull requests: the lock change, which
  the owner approves, and the work, which does not touch the lock.
- The current judge must be extracted into a small derivation. Until then, the
  lock covers the 45 modules that `replay_tiers.py` imports, and most changes
  to `conformance/` need an owner review.
- After decisions 2 to 4 are in force, the obstacle checks are removed: the
  Python fast path and the `pinned` suite (95 s on Linux), the binding and
  digest tests without a protected anchor, and the report validators. Full
  validation of a corpus runs once, in the pull request that locks it.
- The verdict job adds runner time but runs in parallel with the current job.
  It replaces the frozen replay in that job instead of repeating it.
- Product-trust tests are external-behavior tests and run in every CI scope.

## Alternatives considered

- **More in-repository checks** (stricter pins, more denominators, test-count
  checks). Rejected: each check lives where the agent writes, so an agent can
  change it together with what it checks.
- **Protect all of `conformance/` and `tests/`.** Rejected: 85% of recent pull
  requests would need an owner review, so approvals become a formality.
- **Protect the judge's source files in `CODEOWNERS` instead of a lock.**
  Rejected: the list must follow every import of the judge, and a missing
  helper module is a hole. The derivation path covers all inputs.
- **Required workflows from a protected repository** (organization rulesets).
  This removes `.github/workflows/` from the protected set and lowers the review
  load to about 21%. GitHub documents it for Enterprise Cloud only, and the
  organization has a paid plan without Enterprise Cloud (2026-10-12), so it is
  not available.
- **A verdict check from a separate GitHub App.** Required checks are bound to
  the app that reports them, so an Actions job cannot report the verdict. This
  also removes `.github/workflows/` from the protected set, but needs a hosted
  verdict runner. Reconsider if the budget of decision 4 is exceeded.
- **Keep R8 as a review finding.** Rejected: a finding is advisory, and the
  review process cannot close "owner review required".

## Open points

- The extracted judge, its interface to the subject, and how a claim states
  its threshold.
- The time to hash the frozen corpora during evaluation, measured before the
  corpora move into the lock.
- Whether workflow changes become rare enough for the budget of decision 4.
  If not, the verdict check from a separate GitHub App is the next option.
