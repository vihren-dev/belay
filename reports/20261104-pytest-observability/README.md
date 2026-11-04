# Pytest observability implementation acceptance

Date: 2026-11-04. Status: repository implementation checked; service rollout pending.
Audience: the team and reviewers.

The implementation follows [ADR 0028](../../docs/adr-0028-development-observability.md).
The owner authorized using its schema export and a provisional pinned ClickHouse
version while devops issue #47 remains open. These results do not claim live
production connectivity, provisioned credentials or a completed trusted CI upload.

## Repository checks

The initial implementation, commit `a62c89a5`, passed:

- `just test-full`: the Nix report set has 1,429 tests and no failures or errors.
  Output: `/nix/store/gm6h6x2zn5ivk8xzs13rqamk129yi2x7-sqlite-verifier-test-reports`.
  [Per-suite results](nix-tests-full.json) retain counts and elapsed times.
- `just test-scheduled-checks`: 50 writer cases passed.
  Output: `/nix/store/yvqjk5y0wwgq9c6fqyxv90pwqdvr47v8-sqlite-verifier-scheduled-check-reports`.
  [Per-suite results](nix-tests-scheduled.json) retain the counts and elapsed time.
- `just verdict`: output
  `/nix/store/f4dif73ki1545dnfdqd01gpbnlv653vz-sqlite-verifier-verdict`.
- `just test-nix`: all 87 selected checks passed, including real source identities,
  failed targets, native platform evaluation and the new narrow observability target.

Subsequent commits corrected the explicit upload deadline, host process-group
handling and propagation of the spool to nested pytest processes, and named
delivery limits. Their focused regressions passed. The final integration output
at commit `e69981ee` is
`/nix/store/dpnizll0yllaphlbsc1r5r18yid1cbwk-sqlite-verifier-test-observability-1`:
one test passed in 0.763 seconds against ClickHouse 26.8.7.19-lts. It stopped
background merges, replayed identical observations, checked immediate unique-view
counts and stored native data, then verified that a fresh execution increased counts.
The full/scheduled outputs above predate those small follow-up corrections; they
are not represented as builds of the final revision.

Local development checks exercised discovered parametrized tests, failed and
concurrent sessions, uncertain acknowledgements, incomplete/malformed records,
producer locks, CI archive validation and host process-group behavior. A nested
pytest check verified that copied temporary harnesses use the parent spool.
These host observations are integration diagnostics, not conformance evidence.
The focused reporting/harness checks took less than eight seconds on this machine.

## One-time Nix commissioning

A temporary source tree registered a new suite through the common factory, with
two newly discovered parametrized cases and no test-specific reporting code.
The shared host runner built each variant and recovered its reports.
[The recorded identities and derivations](commissioning.json) show:

| Variant | Observed behavior |
| --- | --- |
| Fresh | Two call reports and a completed session |
| Cached | Same output, execution UUID, timestamp and report bytes |
| Relevant test edit | New derivation and execution UUID |
| Assertion failure | Build stayed failed; both call reports and SessionFinish were recovered |
| Abrupt exit | Build stayed failed; the first call report survived, with no SessionFinish |

The disposable fixture sources and targets were outside the checkout and removed
after recording these results. The retained derivation paths identify the exact
builder inputs while those paths remain in the Nix store. Permanent regression
tests cover the integration; no demonstration suite was added to normal tests.
Existing historical experiments remain unchanged with their reproduction material.

## Deployment follow-up

Devops must return the deployed schema revision, server version, endpoint,
credentials, network/CA setup and commissioning evidence. Confirm or update the
provisional schema/server pair before enabling upload. Configure the protected
`observability` GitHub environment as described in the
[developer guide](../../docs/test-observability.md). The trusted upload workflow
becomes active after its code reaches `main`. Live local/CI queries, permissions,
persistence and backup/restore commissioning remain deferred by owner decision.
