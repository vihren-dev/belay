"""Publish the authored coverage cases of `printf` and `format` as a new corpus (ADR 0015, slice 6).

`python -m conformance.printf_evidence --output DIRECTORY` records the cases of
`conformance.authored_printf` natively as version 5 records with outputs and writes them as
corpus version 41 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_printf import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_printf.py"),
    source_name="authored-printf", part="printf", corpus_version=41, evidence_kind="printf-coverage")
"""The coverage corpus of printf: version 41, after the corpus of the aggregates."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of printf."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of printf natively and write them as a new corpus "
                                   "directory.")
