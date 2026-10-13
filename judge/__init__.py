"""The judge of development claims (ADR 0011, `docs/adr-0011-product-trust-and-development-integrity.md`).

The judge compares what native SQLite recorded in the frozen corpora with what the subject
(the frontend and the model) predicts, and applies the claims in `judge/claims.json`.
Per statement it compares the tables, the transaction state, the primary result code and,
for records of native version 5, the error phase (`prepare` or `step`).
It uses only the standard library and its own modules, so that a change to the subject
cannot change a verdict. `integrity/judge.lock.json` locks the judge with its inputs.
"""
