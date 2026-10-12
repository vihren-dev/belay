# Convert the frozen review log to record files

Created 2026-10-11. Status: DONE ([PR #87](https://github.com/vihren-dev/sqlite-verifier/pull/87) and the conversion-rule removal).
Step 3 of the review-log change agreed with the owner on 2026-10-11 (see
[20261011-review-log-per-record-files.task.md](20261011-review-log-per-record-files.task.md)).
Step 2 is done: `just review-log-frozen` reported on 2026-10-11 that no
unmerged branch or workspace has frozen-log lines that `main` lacks.

## Outcome

1. Every record of `reviews/log.jsonl` exists as a record file at the path
   that `tools/review_records.py` gives it. Identical duplicate lines (34,
   left by earlier merges) become one file. `reviews/log.jsonl` is deleted.
2. No code reads, writes or mentions the frozen log: `tools/review_records.py`
   reads only record files, and `just review-log-frozen` with
   `tools/review_log_frozen.py` is removed.
3. `tools/review_log_check.py` checks only record files. For this change
   only, a base commit that still has `reviews/log.jsonl` passes when the
   head no longer has it and every one of its records exists as a record file
   with the same content. A follow-up change removes this rule after this
   one is on `main`.
4. CI scope: `reviews/log.jsonl` is no longer a record path.
5. `AGENTS.md` and `docs/ci.md` describe only record files. The status
   files of both review-log tasks record step 2 and step 3.
6. `just review-stats` counts each review once. Before, duplicated lines
   counted a review twice; the report of the converted records must equal
   the report of the deduplicated frozen log.

## Tests

- Conversion: the set of records (as canonical JSON) in the record files
  equals the set of distinct lines of the old `reviews/log.jsonl`.
- Statistics: the `review-stats` table from the record files equals the table
  from the old log after removing duplicate lines.
- Check: deleting the base log passes when all its records are files; it fails
  and names the missing record when one is absent; a head that still has
  `reviews/log.jsonl` fails as a file that is not a record.
- Reading, writing, CI scope and the review command keep their tests, without
  frozen-log cases.
- The CI check passes on the converted head against `main`.

## Key points

- Merged pull requests and open branches: PR CI runs on GitHub's merge of the
  branch into `main`. Open branches did not change `reviews/log.jsonl` after
  step 2, so the deletion merges without a conflict.
- `review_stats.latest_outcomes` orders resolutions by date, then position.
  `read_records` orders files by date, reviews first, then path, so the
  result does not depend on the old line order.
- Keep every file under 200 lines.
