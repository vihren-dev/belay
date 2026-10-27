"""The SQL checker on claims about programs (ADR 0017, S6): triples, equivalences and the migration pattern."""

import re
import shutil
from pathlib import Path
from textwrap import indent

import pytest

from tests.lean_server_support import compile_helper_module
from tests.runtime_support import run_command
from tests.s6_check_support import CHAIN_TIMEOUT_SECONDS, final_rows, replays, split_blocks
from tests.surface_assertion_examples_test import check_module_chain
from tests.surface_execution_test import ALLOWED_PROOF_AXIOMS
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3")]

PROVED = {"triple-proved", "equiv-proved"}
"""The cases for which the checker finds a proof."""

FALSE = {"triple-false", "lean-continuation-false", "equiv-false", "equiv-at-false", "equiv-shrink-exhausted",
         "observation-false", "view-false", "migration-star-false"}
"""The cases for which the checker finds a counterexample that SQLite replays."""

UNKNOWN = {"budget-unknown", "undecidable-unknown", "migration-lookup-unknown"}
"""The cases for which the checker finds neither a proof nor a counterexample."""

PROOF_STATEMENTS = {
    "triple-proved": """FreshEnsures (send bump) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion))""",
    "equiv-proved": "Sql.Equiv (send bump) (send bump)",
}
"""The claim of each proved case, as the test states it again to check the printed script."""


@pytest.fixture(scope="module")
def blocks(runtime_root: Path, tmp_path_factory: pytest.TempPathFactory) -> dict[str, str]:
    """The output of each case of the fixture module `S6CheckPrograms`, by label."""
    directory = tmp_path_factory.mktemp("s6-check-programs")
    output = check_module_chain(runtime_root, directory, (
        ("S6RulesEffects", 3), ("S6RulesQueryPattern", 8), ("S6CheckLabels", 0), ("S6CheckPrograms", 0)),
        timeout=CHAIN_TIMEOUT_SECONDS)
    found = split_blocks(output)
    assert set(found) == PROVED | FALSE | UNKNOWN, output
    return found


def test_each_case_has_the_outcome_that_its_claim_deserves(blocks: dict[str, str]) -> None:
    """The checker proves the true triple and the equivalence of a program with itself, refutes the false
    triple, the false equivalences and the false migration claim, and reports unknown when the budget is
    too small, when the postcondition has no decision procedure, and when the claim is true for every
    candidate but has no default proof. Unknown is never reported as false."""
    for name in PROVED:
        assert blocks[name].startswith("SQL check: proved."), (name, blocks[name])
    for name in FALSE:
        assert blocks[name].startswith("SQL check: false."), (name, blocks[name])
    for name in UNKNOWN:
        assert blocks[name].startswith("SQL check: unknown;"), (name, blocks[name])
        assert "Database:" not in blocks[name] and "SQLite replay" not in blocks[name], blocks[name]


def test_false_triple_names_the_database_the_environment_and_the_failing_run(blocks: dict[str, str],
                                                                             tmp_path: Path) -> None:
    """The witness of a false triple names the initial database, the complete environment and the failing
    observation, and native SQLite leaves the row that the model's run leaves: the quantity 6, not 7."""
    block = blocks["triple-false"]
    assert "Database: sample" in block and "Environment: Check.candidateEnvironment" in block, block
    assert "Failing observation: The check fails on the actual run of the program." in block, block
    assert "Model outputs: [done 1]" in block and "Note:" not in block, block
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    [script] = replays(block)
    assert final_rows(sqlite, tmp_path, "triple", script, "\nSELECT id, qty FROM items;\n") == [[1, 6]]


def test_lean_continuation_is_described_as_the_model_run_of_the_whole_program(blocks: dict[str, str]) -> None:
    """A program with a continuation in Lean code gives a counterexample whose report names the quantified
    input and says that SQLite ran the scripts and not the whole program; the failure is not shown as a
    failure of one native statement."""
    block = blocks["lean-continuation-false"]
    assert "n: Value.null" in block, block
    assert "Note: The program runs Lean code after the scripts of this replay" in block, block
    assert "The model's run of the whole program gives the failing result." in block, block
    assert "Failing observation: The check fails on the actual run of the program." in block, block


def test_false_equivalences_show_the_native_difference(blocks: dict[str, str], tmp_path: Path) -> None:
    """The refutation of an equivalence names the database and says that the runs differ, and native SQLite
    leaves different rows for the two programs: the quantity 6 for the first and 7 for the second. The
    outputs of the two runs are equal, so the text says that the value or the connection differs, and does not
    claim that the value is the same."""
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    for name in ("equiv-false", "equiv-at-false"):
        block = blocks[name]
        assert "Database: sample" in block, block
        assert ("Failing observation: The actual runs of the two programs differ at this context, in the "
                "returned value or in the connection that they leave. The outputs of the two runs are equal.") in block, block
        first, second = replays(block)
        inspect = "\nSELECT id, qty FROM items;\n"
        assert final_rows(sqlite, tmp_path, f"{name}-first", first, inspect) == [[1, 6]], block
        assert final_rows(sqlite, tmp_path, f"{name}-second", second, inspect) == [[1, 7]], block


def test_explanation_names_what_the_relation_compares(blocks: dict[str, str]) -> None:
    """The explanation depends on the relation of the claim. The observation relation, which ignores the
    connection, says that the returned values differ and never blames the connection. The relation with views
    says that the views project the runs to different observations. Both texts show the equal outputs."""
    observation = blocks["observation-false"]
    assert ("Failing observation: The actual runs of the two programs differ at this context, in the returned "
            "value. The outputs of the two runs are equal.") in observation, observation
    assert "connection" not in observation.split("Database construction:")[0], observation
    views = blocks["view-false"]
    assert ("Failing observation: The views of the claim project the actual runs of the two programs to "
            "observations that differ at this context.") in views, views


def test_refutation_survives_the_exhaustion_of_the_shrinking(blocks: dict[str, str]) -> None:
    """With a budget that the shrinking of the witness cannot finish in its share, the checker still reports
    the certified refutation with its database and failing observation, and not unknown: the exhaustion of the
    shrinking, which the checker runs after the explanation, does not discard an accepted refutation."""
    block = blocks["equiv-shrink-exhausted"]
    assert "Database: sample" in block and "Failing observation:" in block, block
    assert len(replays(block)) == 2, block


def test_migration_claim_about_a_read_of_all_columns_is_refuted(blocks: dict[str, str], tmp_path: Path) -> None:
    """The preservation claim for the read of all columns is false, because the migration adds a column. The
    report names the initial database of the closed claim and the different outputs of the runs, and native
    SQLite shows the added column after the migration."""
    block = blocks["migration-star-false"]
    assert "Initial database of the run: sample." in block, block
    assert 'First program: returns a value; outputs [rows [[1, "Ada", 5]]].' in block, block
    assert "Note: The program runs Lean code after the scripts of this replay" in block, block
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    before, migration = replays(block)
    inspect = "\nSELECT * FROM items;\n"
    assert final_rows(sqlite, tmp_path, "star-before", before, "") == [[1, "Ada", 5]]
    assert final_rows(sqlite, tmp_path, "star-after", migration, inspect) == [[1, "Ada", 5, "ada"]]


@pytest.mark.parametrize("name", sorted(PROVED))
def test_printed_proof_checks_again_with_ordinary_axioms(runtime_root: Path, tmp_path: Path, blocks: dict[str, str],
                                                         name: str) -> None:
    """The script that the checker prints for a proved claim proves the claim again in a new theorem, without
    a search, and the theorem uses only ordinary logical axioms."""
    proof = blocks[name].split("Checked proof: by ", 1)[1]
    assert "sql_auto" not in proof, proof
    extra = compile_helper_module(runtime_root, tmp_path, "S6RulesEffects",
                                  (FIXTURES / "S6RulesEffects.lean").read_text())
    file = tmp_path / "Printed.lean"
    file.write_text(f"""import S6RulesEffects
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
namespace S6RulesEffects
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database
theorem printed : {PROOF_STATEMENTS[name]} := by
{indent(proof, '  ')}
#print axioms printed
end S6RulesEffects
""")
    setup = module_setup(runtime_root, tmp_path, module="Printed", extra_modules=extra)
    result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}", str(file)],
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    audit = re.search(r"'S6RulesEffects.printed' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
                      result.stdout)
    assert audit is not None, result.stdout
    assert set(filter(None, map(str.strip, (audit[1] or "").split(",")))) <= ALLOWED_PROOF_AXIOMS, result.stdout
    assert "sorry" not in result.stdout, result.stdout
