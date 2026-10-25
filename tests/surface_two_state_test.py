"""Native SQLite is the oracle for `Script.observeTwoState`, the read-only observation of a query over
the current database and a fixed initial database named `before` (ADR 0017, S6)."""

import hashlib
import json
from dataclasses import dataclass, field
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import CommandResult, run_command
from tests.surface_support import surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3")]
LEAN_SECONDS = 600
NATIVE_SECONDS = 10
HEADER = """import Belay
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The result column names of a query that the two-state resolver accepts. -/
def namesOf (script : Script) (initial current : Database.Raw) : Option (List String) :=
  match script.statements with
  | [(statement, _)] => match statement.asQuery? with
    | some (query, subqueries) =>
      match resolveTwoState runContext initial.catalog current.catalog query subqueries with
      | .ok (.query resolved _, _) => some resolved.names
      | _ => none
    | none => none
  | _ => none
"""


@dataclass(frozen=True)
class Case:
    """One scenario: setup of both databases, the queries, and changes of the current database."""
    name: str
    initial: str
    current: str
    queries: tuple[str, ...]
    changes: tuple[str, ...] = field(default=())


INT = "CREATE TABLE t(a INTEGER); "
CASES = [
    Case("different-rows", INT + "INSERT INTO t VALUES(1),(2);", INT + "INSERT INTO t VALUES(3);",
         ("SELECT a FROM before.t ORDER BY a", "SELECT a FROM t ORDER BY a", "SELECT before.t.a FROM before.t ORDER BY a"),
         ("INSERT INTO t VALUES(4)", "DELETE FROM t")),
    Case("dropped-current", INT + "INSERT INTO t VALUES(1),(2);", INT, ("SELECT a FROM before.t ORDER BY a",),
         ("DROP TABLE t",)),
    Case("equal-rows", INT + "INSERT INTO t VALUES(1),(2);", INT + "INSERT INTO t VALUES(1),(2);",
         ("SELECT a FROM before.t ORDER BY a", "SELECT a FROM t ORDER BY a"), ("UPDATE t SET a = a + 10",)),
    Case("absent-tables", "CREATE TABLE u(b);", "", ("SELECT a FROM before.t", "SELECT b FROM before.u")),
    Case("positions-and-schemas", "CREATE TABLE u(b INTEGER); " + INT + "INSERT INTO t VALUES(5),(6);",
         "CREATE TABLE t(x INTEGER, y INTEGER); INSERT INTO t VALUES(1,2);",
         ("SELECT a FROM before.t ORDER BY a", "SELECT x FROM t", "SELECT a FROM t", "SELECT * FROM before.t ORDER BY a")),
    Case("rowid-alias", "CREATE TABLE t(id INTEGER PRIMARY KEY, a INTEGER); INSERT INTO t VALUES(1,10),(2,20);",
         "CREATE TABLE t(a INTEGER, id INTEGER); INSERT INTO t VALUES(7,8);",
         ("SELECT id, a FROM before.t ORDER BY id", "SELECT a, id FROM t")),
    Case("generated-column", "CREATE TABLE t(a INTEGER, b INTEGER AS (a + 1)); INSERT INTO t(a) VALUES(1),(2);", INT,
         ("SELECT a, b FROM before.t ORDER BY a",)),
    Case("collation", "CREATE TABLE t(a TEXT COLLATE NOCASE); INSERT INTO t VALUES('x');",
         "CREATE TABLE t(a TEXT); INSERT INTO t VALUES('x');",
         ("SELECT a FROM before.t WHERE a = 'X'", "SELECT a FROM t WHERE a = 'X'")),
    Case("affinity", INT + "INSERT INTO t VALUES(1);", "CREATE TABLE t(a); INSERT INTO t VALUES(1);",
         ("SELECT a FROM before.t WHERE a = '1'", "SELECT a FROM t WHERE a = '1'")),
    Case("joins", INT + "INSERT INTO t VALUES(1),(2);", INT + "INSERT INTO t VALUES(2),(3);",
         ("SELECT x.a, i.a FROM t AS x LEFT JOIN before.t AS i ON i.a = x.a ORDER BY x.a",
          "SELECT i.a, c.a FROM before.t AS i JOIN t AS c ON i.a = c.a",
          "SELECT t.a FROM t, before.t", "SELECT a FROM before.t, t"), ("INSERT INTO t VALUES(1)",)),
    Case("correlated", INT + "INSERT INTO t VALUES(1),(2);", INT + "INSERT INTO t VALUES(2),(3);",
         ("SELECT x.a, (SELECT count(*) FROM before.t AS i WHERE i.a = x.a) AS n FROM t AS x ORDER BY x.a",
          "SELECT a FROM t WHERE a IN (SELECT a FROM before.t) ORDER BY a",
          "SELECT a FROM t AS x WHERE EXISTS (SELECT 1 FROM before.t AS i WHERE i.a > x.a) ORDER BY a"),
         ("DELETE FROM t",)),
    Case("cte-shadowing", INT + "INSERT INTO t VALUES(1),(2);", INT + "INSERT INTO t VALUES(3);",
         ("WITH t AS (SELECT 9 AS a) SELECT a FROM before.t ORDER BY a", "WITH t AS (SELECT 9 AS a) SELECT a FROM t")),
    Case("views", INT + "INSERT INTO t VALUES(1),(2); CREATE VIEW v AS SELECT a FROM t;", INT + "INSERT INTO t VALUES(3); CREATE VIEW v AS SELECT a FROM t;",
         ("SELECT a FROM before.v ORDER BY a", "SELECT a FROM v")),
    Case("except", INT + "INSERT INTO t VALUES(1),(2);", INT + "INSERT INTO t VALUES(2),(3);",
         ("SELECT a FROM before.t EXCEPT SELECT a FROM t ORDER BY a", "SELECT a FROM t EXCEPT SELECT a FROM before.t ORDER BY a")),
    Case("alias-before", INT + "INSERT INTO t VALUES(1);", INT + "INSERT INTO t VALUES(2);",
         ("SELECT before.a FROM t AS before", "SELECT before.a FROM before.t AS before", "SELECT before.t.a FROM t AS before")),
    Case("quoted-dot", 'CREATE TABLE "a.b"(a INTEGER); INSERT INTO "a.b" VALUES(4);', INT,
         ('SELECT a FROM before."a.b"', "SELECT a FROM before.a")),
    Case("aggregates", INT + "INSERT INTO t VALUES(1),(5);", INT, ("SELECT count(*), max(a) FROM before.t",)),
]


def native(sqlite: str, directory: Path, current: Path, copy: Path, query: str) -> list[object]:
    """The rows `[names, rows]` of the query with the copy attached as `before`, or `["error", code]`."""
    sql = f"ATTACH 'file:{copy}?mode=ro&immutable=1' AS before; {query};"
    result = run_command([sqlite, "-batch", "-json", str(current), sql], cwd=directory, timeout=NATIVE_SECONDS)
    if result.returncode:
        return ["error", result.returncode]
    pairs = json.loads(result.stdout or "[]", object_pairs_hook=lambda items: items)
    names = [name for name, _ in pairs[0]] if pairs else None
    return [names, [[value for _, value in row] for row in pairs]]


def value(cell: object) -> str:
    """The Lean value of a native JSON cell."""
    if cell is None:
        return ".null"
    if isinstance(cell, bool) or isinstance(cell, float):
        raise AssertionError(f"The case uses a value the test does not render: {cell!r}")
    if isinstance(cell, int):
        return f".integer {cell}"
    assert isinstance(cell, str)
    return ".text " + json.dumps(list(cell.encode()))


def expectation(answer: list[object]) -> tuple[str, str]:
    """The Lean outputs for the rows of a native answer and the names of its columns."""
    if answer[0] == "error":
        return f"Output.error {answer[1]}", "none"
    names, rows = answer
    if names is None:
        return "Output.rows []", "none"
    cells = "[" + ", ".join("[" + ", ".join(value(cell) for cell in row) + "]" for row in rows) + "]"
    return f"Output.rows {cells}", "some " + json.dumps(names)


def example(query: str, initial: str, current: str, answer: list[object], swapped: bool = False) -> str:
    """Lean examples that the observation agrees with the native answer; `swapped` reads the current
    database for the initial source, the mutation that the test must see fail."""
    outputs, names = expectation(answer)
    first, second = (current, initial) if swapped else (initial, current)
    script, one, two = f'(sql r#"{query}"#)', f'(db! r#"{first}"#).raw', f'(db! r#"{second}"#).raw'
    text = f"example : {script}.observeTwoState {one} ({two}.connection) = {outputs} := by decide +kernel\n"
    if names != "none":
        text += f"example : namesOf {script} {one} {two} = {names} := by decide +kernel\n"
    return text


def lean(runtime_root: Path, directory: Path, name: str, text: str) -> CommandResult:
    """Elaborate a fixture that imports `Belay`."""
    source = directory / f"{name}.lean"
    source.write_text(HEADER + text)
    return run_command(surface_command(runtime_root, source, directory), cwd=directory, timeout=LEAN_SECONDS)


def setup(sqlite: str, directory: Path, database: Path, sql: str) -> None:
    """Run setup SQL on a database file of the native engine; a failure is a defect of the case."""
    result = run_command([sqlite, str(database), sql or "SELECT 1;"], cwd=directory, timeout=NATIVE_SECONDS)
    assert result.returncode == 0, result.diagnostic()


def gather(sqlite: str, directory: Path) -> tuple[str, list[tuple[Case, str, str, list[object]]]]:
    """Run every case natively; the copy of the initial file must not change, whatever the current
    database does. Return the Lean examples and the first case's native answer."""
    examples = ""
    firsts: list[tuple[Case, str, str, list[object]]] = []
    for case in CASES:
        setup(sqlite, directory, directory / f"{case.name}-initial.db", case.initial)
        copy = directory / f"{case.name}-copy.db"
        shutil.copy(directory / f"{case.name}-initial.db", copy)
        digest = hashlib.sha256(copy.read_bytes()).hexdigest()
        current_file, current = directory / f"{case.name}-current.db", case.current
        setup(sqlite, directory, current_file, current)
        for step in range(len(case.changes) + 1):
            if step:
                current += " " + case.changes[step - 1] + ";"
                setup(sqlite, directory, current_file, case.changes[step - 1])
            for query in case.queries:
                answer = native(sqlite, directory, current_file, copy, query)
                examples += example(query, case.initial, current, answer)
                if not firsts and answer[0] != "error":
                    firsts.append((case, query, current, answer))
        assert hashlib.sha256(copy.read_bytes()).hexdigest() == digest, case.name
    return examples, firsts


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


def test_two_state_theorems_use_no_forbidden_axioms(runtime_root: Path, tmp_path: Path) -> None:
    """The proofs of the conservative-extension and independence theorems of the two-state observation
    depend on no `sorryAx`, `Lean.ofReduceBool` or native code (code under test: the Lean proofs of
    the two-state modules)."""
    result = lean(runtime_root, tmp_path, "Axioms", "".join(f"#print axioms {name}\n" for name in PUBLIC_THEOREMS))
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout.count("depends on axioms") + result.stdout.count("does not depend on any axioms") == \
        len(PUBLIC_THEOREMS), result.stdout
    assert all(term not in result.stdout for term in ("sorryAx", "ofReduceBool", "_native")), result.stdout
