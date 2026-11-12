import Belay

/-! A fixture of `tests/surface_name_trace_test.py`: the paths of the name trace of the model
(`resolveStatementTraced`) locate names in the translated SQL. The fixture translates statements,
resolves them one after the other, and checks for each exact occurrence with a name that the range which
`Span.select` gives for its path is the text of that name, with quotes. The statements cover the
queries and writes that the trace covers. The file fails to elaborate when a check fails. -/

open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Translation

/-- The statements of the SQL with the default release's grammar; a refusal fails the check. -/
def translated (text : String) : IO (Array (Located Syntax.Statement)) := do
  let grammar ← IO.ofExcept ((selectGrammar (← loadedMetadata) Release.default).mapError IO.userError)
  match ← translate grammar text.toUTF8 with
  | .ok items => return items.map (·.statement)
  | .error refusal => throw <| IO.userError s!"the translation refuses {text}: {refusal.message}"

/-- The text of the range that the path selects in the statement. -/
def textAt (text : String) (item : Located Syntax.Statement) (path : List Nat) : String :=
  let (start, stop) := item.span.select path
  (String.fromUTF8? (text.toUTF8.extract start stop)).getD ""

/-- Fail unless each exact occurrence with a name selects the token of its name; give the number of
occurrences checked. -/
def checkNames (text : String) (item : Located Syntax.Statement) (trace : NameTrace) : IO Nat := do
  let mut checked := 0
  for occurrence in trace do
    match occurrence.name with
    | none => pure ()
    | some name =>
      if occurrence.exact then
        let found := textAt text item occurrence.path
        unless Identifier.ofString (dequote found) == name do
          throw <| IO.userError s!"{text}: path {occurrence.path} selects {repr found}, not the name"
        checked := checked + 1
  return checked

/-- Resolve the statements one after the other, each translated alone, and check the names of each; give
the number of names checked in each statement. -/
def checkScript (statements : List String) : IO (List Nat) := do
  let mut state : ResolveState := { catalog := [] }
  let mut counts := []
  for text in statements do
    let #[item] ← translated text | throw <| IO.userError s!"expected one statement in {text}"
    let (result, trace) := resolveStatementTraced { profile := Profile.pinned, mode := .execution } state item.value
    counts := counts ++ [← checkNames text item trace]
    match result with
    | .ok (_, next) => state := next
    | .error _ => pure ()
  return counts

#eval show IO Unit from do
  let counts ← checkScript [
    "CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT UNIQUE, c REAL);",
    "CREATE TABLE u(a INTEGER, d TEXT);",
    "CREATE VIEW v AS SELECT a, b FROM t;",
    "SELECT t.a, \"b\" FROM t WHERE c > 1 AND b = 'x' GROUP BY a, b HAVING a > 0 ORDER BY b;",
    "SELECT x.a FROM t AS x JOIN u USING (a) WHERE d IS NULL;",
    "SELECT a FROM t NATURAL JOIN u;",
    "SELECT a FROM t WHERE EXISTS (SELECT 1 FROM u WHERE u.a = t.a);",
    "WITH w(p) AS (SELECT a FROM t) SELECT p FROM w WHERE p IN (SELECT a FROM w);",
    "SELECT a FROM v;",
    "SELECT a FROM t UNION SELECT a FROM u ORDER BY a;",
    "INSERT INTO t(a, b) VALUES (1, 'x') ON CONFLICT(a) DO UPDATE SET b = excluded.b RETURNING a;",
    "UPDATE t SET c = c + 1 WHERE a = 2 RETURNING b;",
    "DELETE FROM u WHERE d = 'q';",
    "SELECT zz FROM t;",
    "SELECT \"zz\" FROM t;",
    "DELETE FROM absent WHERE e = 1;"]
  -- The CREATE statements have no trace (a documented gap); the zero counts keep that visible.
  unless counts == [0, 0, 0, 10, 7, 3, 7, 9, 2, 5, 8, 5, 2, 2, 2, 1] do
    throw <| IO.userError s!"the statements have {counts} names with exact paths"
