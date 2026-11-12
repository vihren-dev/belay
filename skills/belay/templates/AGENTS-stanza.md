## SQL claims with Belay

This project proves facts about its SQLite schema and migrations with
[Belay](https://github.com/vihren-dev/belay), a Lean library.

- The SQL is in `db/`. The claims are Lean files in `Claims/`. The schema
  database is `shop` of `Claims/Schema.lean`.
- Before you change the SQL or the claims, read
  `.lake/packages/belay/skills/belay/SKILL.md` and follow it. If the file is
  absent, run `lake update`.
- State a claim for each SQL change, with the schema `shop` as its premise,
  and run `#sql_check` before you prove.
- Do not make a claim weaker to pass the check. Report each change of a claim.
- `unknown` is not `proved`. Do not use `sorry` and do not add an axiom.
