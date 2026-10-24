# Derived-source prediction and evidence record

Date: 2026-10-24. Task: `plans/20261024-query-sources.task.md`, part 1.
Status: pending final full/verdict acceptance. Ordinary CTEs and views remain.

## Frozen comparison

The pre-edit implementation is carry `8a89208ff0f1`. Its Nix predictions are
`/nix/store/qwfgz46d1pyd10xiypmka4kixvx38k2b-sqlite-verifier-predictions`.
Its Nix verdict is
`/nix/store/srv5lc3gnn1s9wzfjy1ilrzsb2ws0881-sqlite-verifier-verdict`.

The implemented model is `c64d8b50316c387f1f4879ef12f45014cb7d5559`.
Its Nix predictions are
`/nix/store/xar2y93h71ffx1ccrjvy906936hk4ahj-sqlite-verifier-predictions`.
The subsequent acquisition fix and tests change no Lean execution or prediction.
Each artifact was built with `nix-build integrity/judge.nix -A predictions`;
the baseline verdict used `-A verdict`. Compare decoded records by corpus and
case name, including all fields. [The table](prediction-changes.tsv) lists every
changed record and its classification.

All 76 changed records were previously restricted:

| Classification | Cases |
| --- | ---: |
| Newly supported successful execution | 27 |
| Newly supported SQLite prepare error | 2 |
| Resolution succeeds; execution admission still fails | 3 |
| FROM form remains excluded; its diagnostic changes | 11 |
| Derived source resolves and exposes another existing restriction | 33 |

No previously predicted record changes. The 33 deeper restrictions are 19 bare
aggregate outputs, four outer aggregate references, three GROUP BY expressions,
two other statement forms, two queries of SQLite's catalog tables, two hidden
rowid uses and one DISTINCT function argument.

The three execution restrictions are `json101:json101-23.1:251`,
`json101:json101-23.2:252` and `selectA:selectA-3.97:199`, all in corpus v5.
They have predictions with `supported: false` and are excluded from new claims.
The combined implementation/evidence predictions are at
`/nix/store/qjij3iya9bpd9mfl0mmln91wnyqcb80q-sqlite-verifier-predictions`.
Every previous corpus file is byte-identical to the implemented model's artifact;
the combined artifact adds v53. Its Nix verdict passed at
`/nix/store/6h8hi4b2c0z3fkxjamwix6508l30dz9i-sqlite-verifier-verdict`.
It confirms all 29 agreement gains: corpus v4 rises from 673 to 675, and v5 from
2,946 to 2,973. All prior agreements and claims survive. No corpus has a
DISAGREE or HARNESS_ERROR. The table includes each before/after Nix verdict.
The final full/verdict gates must follow the last independent review.

## Authored evidence

Corpus v53 currently has 42 derived-source inputs. Native SQLite supplies all
observations. The Nix kernel coverage check proves 38 agreements and four
explicit model restrictions at
`/nix/store/804jb5hkkrpn3ahxd21x556aajwz13m2-sqlite-verifier-test-query-source-coverage-1`.
The four restrictions cover compound representatives, arbitrary LIMIT membership,
uncertainty visible only in the second column, and fallible source evaluation.

The corpus publisher's Nix round trip passed at
`/nix/store/9dzarjyyg9iq1r1n029b04a7rbbw18ja-sqlite-verifier-test-query-source-writer-1`.
It records fresh native observations, reads the written corpus back unchanged,
replays it, and rejects an attempt to replace the output directory.
The actual v53 shard also passed the complete Nix corpus validation at
`/nix/store/hxi4kmq91n1vpl13nsjbi9cnkj6qw8yq-sqlite-verifier-test-query-source-corpus-1`.

The current cases digest is
`55a322349b037c52e3de15072eede75da30be53536fcb6a67dd29239d79e46d0`.
This is an unpublished draft corpus. It remains mutable until the CTE and view
parts add their evidence. Corpus, claim and lock changes are separate from the
implementation and need owner approval before merge.
