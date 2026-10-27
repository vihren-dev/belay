# Status: schema-script laws

Created 2026-10-27. Status: OPEN.
Task: [task file](20261027-schema-script-laws.task.md).
Specs: ADR 0017 S6; the S6 automation task, part 3 outcome "the rebuild
example", and its status section "Part 3 outcome (a), the rebuild example:
stopped at a gap (2026-10-27)".

## Decisions

- 2026-10-27 (owner): option A of the S6 part 3 gap. A separate task adds the
  general step, frame, translation and success laws, then the rebuild fixture
  proves the three guide claims.

## Progress

- 2026-10-27: task specified on top of S6 automation part 3a (PR #283). The
  implementation starts on a base that contains the derived-column task.
- 2026-10-27: spec review `20261027T130038Z-837cf158` (2 musts: the frame law must exclude a
  cascade of DROP TABLE; the INSERT SELECT success law must require fitting column types). Coordinator
  error: commit d37be705, described as the fix, holds only that review record, because the edit script
  failed before it wrote the file; its review `20261027T130113Z-d37be705` has no findings, and the two
  resolutions were recorded as fixed before the fix existed. The fix is the next commit.
