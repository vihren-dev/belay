"""Native SQLite is the oracle for `Script.observeTwoState`, the read-only observation of a query over
the current database and a fixed initial database named `before` (ADR 0017, S6)."""

from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command
from tests.two_state_support import HEADER, INT, NATIVE_SECONDS, example, expectation, gather, lean, native, setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3")]


def test_observation_agrees_with_native_sqlite(runtime_root: Path, tmp_path: Path) -> None:
    """The observation gives the rows, the column names and the error codes that SQLite gives with
    the initial copy attached as `before`, over a sequence of changes of the current database, and a
    read of the current rows for an initial source fails the same check (code under test:
    `Script.observeTwoState` and the two-state resolver)."""
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=NATIVE_SECONDS)
    assert version.stdout.startswith("3.51.0 "), version.diagnostic()
    examples, firsts = gather(sqlite, tmp_path)
    result = lean(runtime_root, tmp_path, "Agree", examples)
    assert result.returncode == 0, result.diagnostic()
    case, query, current, answer = firsts[0]
    mutated = lean(runtime_root, tmp_path, "Mutated", example(query, case.initial, current, answer, swapped=True))
    assert mutated.returncode != 0, "The mutation that reads current rows for an initial source was not detected"


def test_writes_and_attachments_are_refused(runtime_root: Path, tmp_path: Path) -> None:
    """A write is not observed, an ATTACH statement does not translate, the ordinary run refuses `before`
    instead of reading the current table, and another schema name has a source diagnostic (code under
    test: `Script.observeTwoState`, `Script.runOn` and the translation of schema names)."""
    def refused(script: str) -> str:
        """A Lean example that the observation of the script is `unmodeled`, checked by the kernel."""
        return (f'example : (match {script}.observeTwoState (db! r#"{INT}"#).raw ((db! r#"{INT}"#).raw.connection) with '
                "| .unmodeled _ => true | _ => false) = true := by decide +kernel\n")

    text = refused('(sql r#"INSERT INTO t VALUES(1)"#)') + refused('(sql r#"SELECT a FROM t; SELECT a FROM t"#)')
    text += (f"example : ((db! r#\"{INT}\"#).raw.run (sql r#\"SELECT a FROM before.t\"#)).outputs.all "
             "(fun | .unmodeled _ => true | _ => false) = true := by decide +kernel\n")
    assert lean(runtime_root, tmp_path, "Refused", text).returncode == 0
    for name, sql, message in [("Attach", "ATTACH 'x.db' AS before", ""),
                               ("Schema", "SELECT a FROM temp.t", "A schema name other than before is not modeled")]:
        result = lean(runtime_root, tmp_path, name, f'example := sql r#"{sql}"#\n')
        assert result.returncode != 0 and message in result.stdout, result.diagnostic()
        if name == "Schema":
            assert f"{name}.lean:{HEADER.count(chr(10)) + 1}:" in result.stdout, result.diagnostic()


def test_modeled_write_between_observations(runtime_root: Path, tmp_path: Path) -> None:
    """After a modeled write on the connection, `before.t` still gives the initial rows and `t` gives the
    rows with the write, and a second observation repeats the first, as native SQLite with the initial
    copy attached gives them (code under test: `Script.observeTwoState` on the connection that
    `Database.Raw.run` returns)."""
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    initial, write = INT + "INSERT INTO t VALUES(1),(2);", "INSERT INTO t VALUES(3)"
    setup(sqlite, tmp_path, tmp_path / "initial.db", initial)
    shutil.copy(tmp_path / "initial.db", tmp_path / "copy.db")
    shutil.copy(tmp_path / "initial.db", tmp_path / "current.db")
    setup(sqlite, tmp_path, tmp_path / "current.db", write)
    text = f'def initial : Database.Raw := (db! r#"{initial}"#).raw\n'
    text += f'def written : Connection := (initial.run (sql r#"{write}"#)).connection\n'
    for query in ("SELECT a FROM before.t ORDER BY a", "SELECT a FROM t ORDER BY a"):
        outputs, _ = expectation(native(sqlite, tmp_path, tmp_path / "current.db", tmp_path / "copy.db", query))
        text += f'example : (sql r#"{query}"#).observeTwoState initial written = {outputs} := by decide +kernel\n'
        text += f'example : (sql r#"{query}"#).observeTwoState initial written = ' \
                f'(sql r#"{query}"#).observeTwoState initial written := rfl\n'
    result = lean(runtime_root, tmp_path, "Written", text)
    assert result.returncode == 0, result.diagnostic()


PUBLIC_THEOREMS = [
    "Belay.Sqlite.Model.observeTwoState_ordinary", "Belay.Sqlite.Model.observeTwoState_unqualified_irrelevant",
    "Belay.Sqlite.Model.observeTwoState_initial_irrelevant", "Belay.Sqlite.Model.resolveTwoState_ordinary",
    "Belay.Sqlite.Model.resolvedStepOutput_initial_irrelevant", "Belay.Sqlite.Model.possibleOutput_initial_irrelevant",
    "Belay.Sqlite.Model.Resolved.Query.possibleOn_current_irrelevant",
    "Belay.Sqlite.Model.Resolved.Query.source_initial_irrelevant",
    "Belay.Sqlite.Model.Resolved.Query.source_current_irrelevant",
    "Belay.Sqlite.Model.Resolved.subqueryContext_initial_irrelevant",
    "Belay.Sqlite.Script.observeTwoState_ordinary", "Belay.Sqlite.Script.observeTwoState_single"]
"""The theorems that state the conservative extension and the independence of the two origins."""
FORBIDDEN_AXIOM_TERMS = ("sorryAx", "ofReduceBool", "_native")
"""The axioms and kernel extensions that a proof of these theorems must not use."""


def test_two_state_theorems_use_no_forbidden_axioms(runtime_root: Path, tmp_path: Path) -> None:
    """The proofs of the conservative-extension and independence theorems of the two-state observation
    depend on no `sorryAx`, `Lean.ofReduceBool` or native code (code under test: the Lean proofs of
    the two-state modules)."""
    result = lean(runtime_root, tmp_path, "Axioms", "".join(f"#print axioms {name}\n" for name in PUBLIC_THEOREMS))
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout.count("depends on axioms") + result.stdout.count("does not depend on any axioms") == \
        len(PUBLIC_THEOREMS), result.stdout
    assert all(term not in result.stdout for term in FORBIDDEN_AXIOM_TERMS), result.stdout
