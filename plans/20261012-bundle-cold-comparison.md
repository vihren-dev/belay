# Bundle cold comparison

Created 2026-10-12. Status: PARTIAL; Linux acquisition is held.
Audience: the team and owner reviewing T06.
Task: [bundle readiness](20261006-bundle-readiness.task.md).

All three macOS comparisons establish a regression under the approved
method. This report gives evidence for the owner decision; it does not
accept a slowdown or authorize T06b. Linux results are still required.

## Complete macOS results

Times are seconds. Each row retains nine paired trials, with no excluded
or invalid pair. The difference is preparation plus bundle checking minus
verify. A median paired difference is not the difference of the path medians.

| Case | Verify median | Verify range | Bundle path median | Bundle path range | Paired difference median | Paired difference range | Median interval |
| --- | ---: | --- | ---: | --- | ---: | --- | --- |
| Small success | 2.722 | 2.661–2.786 | 4.150 | 4.136–4.203 | 1.460 | 1.356–1.500 | 1.365–1.489 |
| Checked refutation | 2.806 | 2.729–2.963 | 4.248 | 4.194–4.461 | 1.451 | 1.256–1.552 | 1.411–1.549 |
| Atuin | 11.475 | 11.236–12.076 | 12.891 | 12.793–13.156 | 1.487 | 0.805–1.681 | 1.134–1.570 |

All lower interval bounds are strictly positive. The approved continuation
rule therefore stops each campaign at nine pairs; no campaign extends to 25.
The interval uses ranks 2 and 8 at nine pairs. Fixed-size coverage is
123/128. Simultaneous coverage for the approved nine-to-25 rule is
1,994,151/2,097,152, above 95%.

## Observed stages

These are medians of inclusive spans from the same invocations. The last
two columns are inside preparation. Do not sum these spans as path wall
time: nested stages overlap, and process startup and observation overhead
are also part of the complete path.

| Case | Verify driver | Preparation driver | Bundle-checking driver | Candidate compilation | Bundle export |
| --- | ---: | ---: | ---: | ---: | ---: |
| Small success | 2.624 | 2.427 | 1.509 | 0.734 | 0.315 |
| Checked refutation | 2.695 | 2.509 | 1.511 | 0.789 | 0.319 |
| Atuin | 11.373 | 8.030 | 4.645 | 4.763 | 0.361 |

These observations describe the measured paths. They do not isolate the
cause of the regression or predict an optimized path.

## Method and identities

The production sources are accepted main through `ee6185ce`; the measurement
harness is the reviewed T06 integration. The installed macOS runtime comes
from the complete offline archive, whose SHA-256 is
`10a2a086c4f23764e3453f74953b68a00218df206d095b5faec31e3c99cdf705`.
All 26 actual installed tests pass before acquisition.

Each path has a fresh isolated process and empty proof, compilation and
stage caches. Invocation order alternates. Both paths use identical
installed runtime and protected input bytes, one machine and filesystem,
and a common 300-second whole-path limit. Installation and downloads are
outside timing. Required compilation is inside timing. Operating-system
file caches are not flushed; residency is not observed. Load averages and
this observation limit are retained for each path.

Author checks verify all 27 pairs and 81 invocations against the recorded
baseline identities. They verify raw output hashes, stage source identities,
process boundaries, empty initial caches, alternating order, deadlines and
actual checker results. The refutation checker returns 2, while the public
CLI returns VIOLATED with exit 1. Every interval is recomputed from the
retained complete path durations.

Raw commands, outputs, traces, identity manifests and artifacts remain
local in `build/20261012-t06-installed/`. They are not copied into this
repository. `darwin-verification.json` records the author checks, and
`darwin-stages-summary.json` records the stage summary.

## Linux and decisions

Linux runtime and native gate builds pass. Source acceptance passes 629
tests and 58 subtests, with two explicit optional reviewer-tool skips.
Offline packaging fails its unchanged integrity check because the pinned
Python store path has changed bytes. No failed archive is used for
installed acceptance or measurement. Linux acquisition is held.

Decisions waiting for the owner:

- Whether to repair the exact pinned Linux Python path through Nix and
  retry unchanged packaging.
- Disposition of the measured regressions before cutover, after Linux
  comparisons can also be completed.
