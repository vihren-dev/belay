# Store review records as one file each

Created 2026-10-11. Status: OPEN.
Owner request: `reviews/log.jsonl` causes merge conflicts. Every `just review`
and `just review-resolve` appends to the end of the same file, so two
workspaces that each record a review always conflict in Git and in jj, even
though their records never contradict each other.

This task is step 1 of three that the owner agreed on 2026-10-11:

1. New records go to their own files; `reviews/log.jsonl` is frozen: still
   read, never written. (This task.)
2. Merge to `main`, then rebase every open branch and workspace onto it.
   Branches that already appended to `reviews/log.jsonl` resolve that
   conflict one last time by keeping both sides' lines.
3. When `reviews/log.jsonl` is the same on every unmerged branch and
   workspace, convert its lines to record files, delete it and remove the
   code that reads it. (A later task.)

## Outcome

1. `just review` writes each review record to its own new file under
   `reviews/`, and `just review-resolve` writes each resolution record to its
   own new file. The file path is derived from the record (review id, finding
   number, resolution time), so two workspaces never create the same path in
   practice, and no command ever changes or deletes an existing record file.
   The record contents (fields and values) are the same as today's log lines.
2. Neither command writes `reviews/log.jsonl` any more.
3. Reading the log (`review-resolve`'s finding lookup and `just review-stats`)
   returns the records of `reviews/log.jsonl` plus all record files. A
   finding recorded in the frozen file can still be resolved with a new
   record file. `SQLITE_VERIFIER_REVIEW_LOG` keeps pointing tests away from
   the repository; it now names the reviews directory.
4. `tools/review_log_check.py` (CI, every scope) enforces append-only for
   both forms:
   - `reviews/log.jsonl`: unchanged rule, each base line is present and each
     line is a record. New lines are still accepted, because branches rebased
     in step 2 carry lines written before the switch.
   - Record files: each record file of the base commit is present with
     identical bytes; each record file in the head is a valid record of its
     kind, and its path matches its contents (review id, finding).
   - Any other file under `reviews/` is refused.
5. CI scope selection (`tests/ci_scope.py`) treats record files like the
   frozen log: a change of only records and Markdown documentation selects
   the `docs` scope. Other files under `reviews/` still select `test`.
6. `just review-log-frozen` reports, for `main` and every bookmark, remote
   bookmark and workspace working copy that is not already merged into
   `main`, whether its `reviews/log.jsonl` equals the one on `main`. It
   exits 0 only when all are equal. This is the signal that starts step 3.
7. `AGENTS.md` and `docs/ci.md` describe the record files, the frozen log
   and the check.

## Tests

- Writing: a review with findings and a resolution each create exactly one
  new file at the expected path with the expected record; existing files
  and `log.jsonl` stay byte-identical; writing to an existing path fails
  rather than overwriting.
- Reading: records from the frozen file and from record files are returned
  together, oldest first; a finding that exists only in the frozen file can
  be resolved; `review-resolve` end-to-end through the command line against
  a temporary reviews directory.
- `review-stats` gives the same report for the same records stored in the
  frozen file or as record files.
- Check: a Git fixture repository where a base commit has a frozen log and
  record files; adding record files and appending to the log passes;
  changing or deleting a base record file, a record file with a mismatched
  path, an invalid record, or an unknown file under `reviews/` fails with a
  message naming the file.
- CI scope: record-file paths select `docs`; unknown files under `reviews/`
  select `test`.
- Frozen report: a jj fixture repository with `main`, a merged bookmark with
  an older log, and an unmerged bookmark; exit 1 while the unmerged bookmark's
  log differs, exit 0 after it matches; merged bookmarks are ignored.
- All tests have timeouts; the review-log suites stay well under 10 s.
- A real `just review` and `just review-resolve` run in this repository after
  the change produce record files and leave `log.jsonl` unchanged.

## Key points

- Today's tools: `tools/review_log.py` (record shapes, `append`, `read`,
  `review-resolve`), `tools/review.py` (calls `append`), `tools/review_stats.py`
  (orders resolutions by date, then by position), `tools/review_log_check.py`
  (CI; base commit from `REVIEW_LOG_BASE`, read with `git`), `tests/ci_scope.py`
  (`RECORD_FILES`), `.github/workflows/ci.yml` (runs the check and its tests on
  the host without Nix; the Nix cache key already ignores `reviews/**`).
- A finding id contains `#` (`20261011T085534Z-6bb34bbf#2`); keep `#` out of
  file names.
- The review id is `<UTC second>-<commit[:8]>`. Two reviews of the same
  commit in the same second would collide; refusing to overwrite is enough.
- `review_stats.latest_outcomes` breaks date ties by list position. With
  files, the read order must be deterministic (e.g. sorted by date, then path)
  so the statistics do not depend on the file system.
- CI runs the check with plain `python3` on the host; it must keep using only
  the standard library and `git` (no `jj` on CI). `just review-log-frozen` is a
  local command and uses `jj`.
- Keep every file under 200 lines (`tools/review_log.py` is already 164).
- Step 3 will need the check to accept deleting `log.jsonl` when each of its
  lines exists as a record file. That is not part of this task.
