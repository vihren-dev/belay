"""Publish the authored coverage cases of the expression forms as a new corpus (ADR 0018, slice 2).

`python -m conformance.expression_form_evidence --output DIRECTORY` records the cases of
`conformance.authored_expression_forms` natively as version 5 records with outputs and writes
them as corpus version 43 through `conformance.authored_evidence`.
"""

from pathlib import Path

from conformance import authored_evidence
from conformance.authored_expression_forms import records
from conformance.case_format import Json

CORPUS = authored_evidence.AuthoredCorpus(
    records=records, definitions=Path(__file__).with_name("authored_expression_forms.py"),
    source_name="authored-expression-forms", part="expression-forms", corpus_version=43,
    evidence_kind="expression-form-coverage")
"""The coverage corpus of the expression forms: version 43, after the corpus of subqueries."""


def publish(directory: Path) -> dict[str, Json]:
    """Acquire, store, load and freshly replay a new coverage corpus of the expression forms."""
    return authored_evidence.publish(CORPUS, directory)


if __name__ == "__main__":
    authored_evidence.main(CORPUS, "Record the authored cases of the expression forms natively and write them as a "
                                   "new corpus directory.")
