"""The mutant tables name what each mutant guards (`conformance.mutant_guards`).

A mutant that survives shows that a rule, a restriction or an admission obligation
is untested; the link says which one. The check runs over the real mutant tables and
the model sources, so a renamed declaration or a removed restriction id breaks the
link at once, and over small sources that show each kind of broken link.
"""

from pathlib import Path
from types import ModuleType

import pytest

from conformance import number_mutants, query_mutants, resolve_mutants, write_mutants
from conformance.mutant_guards import guard_problems
from tests.restriction_registry_test import registry_ids

pytestmark = [pytest.mark.unit]
ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize("table", [resolve_mutants, query_mutants, number_mutants, write_mutants],
                         ids=lambda table: table.__name__.rsplit(".", 1)[1])
def test_every_mutant_names_what_it_guards(table: ModuleType) -> None:
    """Every mutant of the table has a guard, and every guard names something that exists."""
    problems = guard_problems(table.MUTANTS, table.GUARDS, ROOT / "packages",
                              set(registry_ids().values()), set())
    assert not problems, problems


def test_broken_links_are_reported(tmp_path: Path) -> None:
    """A guard of the wrong declaration, an unknown restriction or obligation, an unknown kind,
    a mutant without a guard and a guard without a mutant are each reported."""
    (tmp_path / "Rules.lean").write_text("def first : Nat := 1\n\ndef second : Nat := 2\n")
    mutants = {name: ("Rules.lean", "def second : Nat := 2", "def second : Nat := 3")
               for name in ("wrong_rule", "right_rule", "restriction", "obligation", "kind", "unguarded")}
    guards = {"wrong_rule": "rule:first", "right_rule": "rule:second", "restriction": "restriction:missing",
              "obligation": "obligation:missing", "kind": "law:second", "stray": "rule:second"}
    problems = guard_problems(mutants, guards, tmp_path, {"real-value"}, {"present"})
    assert problems == [
        "unguarded: no guard; add it to GUARDS",
        "stray: guard of no mutant; remove it from GUARDS",
        "wrong_rule: its text is not inside the declaration first of Rules.lean",
        "restriction: missing is not a restriction id of RestrictionKind.id",
        "obligation: missing is not an obligation conjunct",
        "kind: law:second does not start with rule:, restriction: or obligation:",
    ]
