"""The judge of development claims (ADR 0011, `docs/adr-0011-product-trust-and-development-integrity.md`).

The judge compares what native SQLite recorded in the frozen corpora with what the subject
(the frontend and the model) predicts, and applies the claims in `judge/claims.json`.
It uses only the standard library and its own modules, so that a change to the subject
cannot change a verdict. `nix/judge.lock.json` locks the judge with its inputs.
"""
