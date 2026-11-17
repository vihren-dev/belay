# A preserved table gives a preserved read

Created 2026-11-17. Issue [#413](https://github.com/vihren-dev/belay/issues/413).
Status: open.

A single library law must prove that a migration preserves a certified
single-table read on every database of the specified schema. The read can
take parameter values. The claim concerns the actual execution and every
successful branch, including INSERT from SELECT alternatives. It allows a
migration to move the table to a different catalog position.

The check must establish the initial read certificate, the migration's
table frame and the resolution of the final read against the moved certificate.
It must connect certificate width to the original table's column count.
The initial and final catalogs must find the protected table under its name.
The caller must be able to discharge the concrete checks by kernel evaluation.

The README sessions preservation theorem must apply this law directly.
Per-example proof modules that build its read certificate, find the table
by name, or prove width from database validity are then unnecessary.
Valid row width and lookup under equal catalogs belong in the library.

## Acceptance

The README's original preservation statement compiles with its original
domain. A migration that can cascade into sessions and a read whose final
resolution differs from the certificate must fail the check. Exercise
the public law and its negative cases with the existing rebuild tests.
The law is for reads supported by ReadAnalysis.analyze. Joins require
different evidence.

## Relevant sources

ReadCertificate.preservesAt accepts branch-specific obligations.
ReadAnalysis.analyze_sound checks the initial certificate.
The schema path of #411 and table frame of #412 supply the final schema
and table for successful branches. The current example constructs these
obligations in RebuildKeepsRead.lean and RebuildKeeps.lean.
