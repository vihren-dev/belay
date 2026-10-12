# Implement ADR 0011: development integrity

Created 2026-10-12. Status: OPEN.
Decision: [ADR 0011](../docs/adr-0011-product-trust-and-development-integrity.md),
accepted by the owner on 2026-10-12 (PR #90). The owner chose interface A
for the judge (a data interface) on 2026-10-12 and turned on code-owner review
in ruleset 23934665 (`require_code_owner_review: true`, one approval).

## Outcome

1. `.github/CODEOWNERS` has two labeled sections and nothing else:
   - Development integrity: `nix/judge.lock.json`, the Nix file that checks
     the lock and defines the verdict, `.github/workflows/` and
     `.github/CODEOWNERS`.
   - Product trust base: the files of ADR 0011 decision 6.
   Its first line describes the actual ruleset.
2. The review checklist has the anchoring condition of ADR 0011 decision 5,
   and has no R8.
3. A claims file states each development claim about the frozen corpora:
   which cases must agree (at least the cases that agree today on corpora v1
   to v3, including the v2 baseline of `reports/20260929-adr4-corpus-v2-progress.json`),
   and that no case is DISAGREE or HARNESS_ERROR on any frozen corpus. A claim
   that only says "nothing disagrees" is not enough: a subject that calls
   every case unsupported must fail a claim with an agreement floor.
4. The subject has a predict command. Its input is one frozen record (profile,
   setup and migration SQL); its output is the predicted observations per
   statement (result or error code, visible and persisted tables, transaction
   state, outputs) as JSON, or "unsupported" with a reason. The frontend and
   the model implement it. The subject never sees the recorded observations.
5. The judge is a small program that compares recorded observations with
   predictions and applies the claims. It uses only the Python standard
   library and its own files. It does not import `belay`, `conformance` or any
   model code, and it does not share types with the model. On corpora v1 to
   v3 and the live model cases it gives the same verdicts as the current
   `classifyCase`.
6. The judge is a Nix derivation whose inputs are the judge, the claims, the
   frozen corpora and the native SQLite build (`nix/sqlite.nix`, with
   `nix/flake.lock`). `nix/judge.lock.json` records its derivation path for
   `x86_64-linux` and `aarch64-darwin`. A Nix file checks the lock during
   evaluation, with content-derived store paths, and stops with an error that
   names the changed input. The same file defines the verdict: the locked
   judge applied to the subject's predictions, in the Nix sandbox.
7. A separate CI job runs the verdict and is a required check of ruleset
   23934665. It runs on every pull request, including documentation-only ones.
   No pull-request code runs on its host: it only evaluates the lock and builds
   the verdict. Its Nix store comes only from substitution, builds, or a cache
   that `main` saves.
8. After 1 to 7 are on `main`, the checks without a protected anchor are
   removed: the pinned fast path in `conformance/pinned_corpora.py` and the
   `pinned` suite, test constants and `reports/` baselines that the claims file
   replaces, binding and digest tests that only make tampering harder, and the
   `reports/*/validate.py` and `check_*.py` validators. Full validation of a
   corpus runs in the pull request that changes the lock.
9. `docs/ci.md` describes the verdict job and the lock; `AGENTS.md` describes
   the two-pull-request flow for a claim change (lock first, then the work).
   ADR 0011 has status ACCEPTED.

## Tests

- Judge: on a small fixture corpus, an honest subject passes; a subject whose
  prediction differs in one observation fails with DISAGREE at that position;
  a subject that answers "unsupported" for every case fails the agreement
  floor; a subject that crashes or writes malformed output fails with
  HARNESS_ERROR.
- Parity: the judge and the current `classifyCase` give equal verdicts on
  corpora v1 to v3 and the live model cases, until the old path is removed.
- Lock: unchanged inputs evaluate; a change to one byte of a corpus, to the
  claims, to the judge code, or to `nix/sqlite.nix` stops evaluation with an
  error that names the input; restoring the input passes again. These run
  against a temporary copy, not the repository.
- Verdict job, end to end on GitHub, recorded in the status file: a pull
  request that changes a corpus without the lock fails the verdict; a pull
  request that changes the lock cannot merge without the owner; a pull
  request that changes only the model and keeps the claims merges after a
  passing verdict without owner review.
- Every remaining test of the removed checks' behavior passes, and CI time is
  recorded before and after.

## Key points

- Today all v4 and v5 records are MODEL_UNSUPPORTED before the model runs
  (`conformance/native_replay.py:79-80`, `nativeVersion == 4`). Real AGREE
  verdicts come only from corpora v1 to v3 and the live cases.
- Today the judge and the subject are one Lean binary, `conformance-runner`
  (`ConformanceRunner.lean`, `VerifierConformance/Case.lean`, `classifyCase`).
  The comparison (`matchesObservation`, `compareSteps`, `compareOutputs`,
  `Outputs.matchesOutput`) uses model types and the model's own `admitted`.
  Interface A moves the comparison to the judge.
- The frontend (`belay/sqlite` and the C parser library) builds the model
  input from SQL in `native_replay.model_case`; under interface A it is part
  of the subject's predict command.
- The judge needs a decoder for frozen records (`native_storage.decoded_record`,
  `native_bindings.decode_rows`, `decode_cell`) without importing
  `conformance`. Keep that decoder in the judge.
- A fixed-output `builtins.path { sha256 = ...; }` is not a check: Nix reuses an
  existing store path without reading the files. Use content-derived paths.
- The derivation path differs per system, and a `nix/flake.lock` update changes
  it: such an update is also a lock change.
- The CI scope `docs` skips Nix today (`tests/ci_scope.py`); the verdict job
  must not.
- Required checks are bound to the GitHub Actions app (integration 15368), so a
  workflow in a pull request could report a check with the verdict's name;
  `.github/workflows/` is code-owned for this reason.
- ADR 0011 budget: if more than about one in five pull requests needs an owner
  review, report it to the owner.
- Keep each file under 200 lines; the judge has a docstring per module that
  links to ADR 0011.
