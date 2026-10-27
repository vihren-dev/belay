import Belay

/-! A fixture of `tests/surface_name_tokens_test.py`: the name tokens that the translation records
in the source text of a result column of a stored view (`Syntax.SourceText`, `Syntax.NameToken`)
stand where the name trace puts the names. A query is translated twice: as the body of
`CREATE VIEW`, which has the tokens, and as a `SELECT`, which the model resolves with a trace
(the stored view resolves as that query; `CREATE` has no trace). For each token, the range that
the view's `Span.select` gives for each of its paths is the token's bytes in the text of the
column. For each exact occurrence of the trace of the SELECT that lies in a result column, the
view's column has a token with the path of the occurrence. The queries cover names of the
expression itself, qualified, quoted and single-quoted names, and the names of subqueries inside
the column. The file fails to elaborate when a check fails. -/

open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Translation

/-- The statements of the SQL with the default release's grammar; a refusal fails the check. -/
def translated (text : String) : IO (Located Syntax.Statement) := do
  let grammar ← IO.ofExcept ((selectGrammar (← loadedMetadata) Release.default).mapError IO.userError)
  match ← translate grammar text.toUTF8 with
  | .ok #[item] => return item.statement
  | .ok _ => throw <| IO.userError s!"expected one statement in {text}"
  | .error refusal => throw <| IO.userError s!"the translation refuses {text}: {refusal.message}"

/-- The result columns of the query of a `CREATE VIEW`. -/
def viewColumns (view : Syntax.Statement) : IO (List Syntax.ResultColumn) :=
  match view with
  | .createView _ _ _ query _ => return query.columns
  | _ => throw <| IO.userError "expected a CREATE VIEW"

/-- Fail unless the tokens of the view's column at `column` stand at the ranges of their paths; give
the number of tokens checked. -/
def checkTokenRanges (view : Located Syntax.Statement) (column : Nat) (source : Syntax.SourceText) : IO Nat := do
  let (textStart, _) := view.span.select [3, 0, column, 2]
  for token in source.tokens do
    for tokenPath in token.paths do
      let path := match token.subquery with
        | none => [3, 0, column, 0] ++ tokenPath
        | some index => [4, index] ++ tokenPath
      let found := view.span.select path
      unless found == (textStart + token.start, textStart + token.stop) do
        throw <| IO.userError s!"token {repr token} selects {found} by {path}, not the range in the text"
  return source.tokens.length

/-- Fail unless each exact occurrence with a name inside the column at `column` has a token with its
path; give the number of occurrences checked. The paths are those of a SELECT: the columns are the
field 0 and the subqueries the field 8. -/
def checkOccurrences (column : Nat) (source : Syntax.SourceText) (trace : NameTrace) : IO Nat := do
  let mut checked := 0
  for occurrence in trace do
    if occurrence.exact && occurrence.name.isSome then
      let own := [0, column, 0]
      if own.isPrefixOf occurrence.path then
        let relative := occurrence.path.drop own.length
        unless source.tokens.any (fun token => token.subquery.isNone && token.paths.contains relative) do
          throw <| IO.userError s!"no token for {occurrence.path} in {repr source.text}"
        checked := checked + 1
      else if let [8, index] := occurrence.path.take 2 then
        if source.tokens.any (·.subquery == some index) then
          unless source.tokens.any (fun token => token.subquery == some index && token.paths.contains (occurrence.path.drop 2)) do
            throw <| IO.userError s!"no token for {occurrence.path} in {repr source.text}"
          checked := checked + 1
  return checked

/-- Create the tables of the script, then check each query as a view body against its own trace; give
the numbers of tokens and of occurrences checked in each. -/
def checkQueries (tables : List String) (queries : List String) : IO (List (Nat × Nat)) := do
  let mut state : ResolveState := { catalog := [] }
  for text in tables do
    let item ← translated text
    match resolveStatement { profile := Profile.pinned, mode := .execution } state item.value with
    | .ok (_, next) => state := next
    | .error _ => throw <| IO.userError s!"{text} does not resolve"
  let mut counts := []
  for query in queries do
    let view ← translated s!"CREATE VIEW v AS {query}"
    let select ← translated query
    let (_, trace) := resolveStatementTraced { profile := Profile.pinned, mode := .execution } state select.value
    let mut tokens := 0
    let mut occurrences := 0
    for (column, index) in (← viewColumns view.value).zipIdx do
      if let .expression _ _ source := column then
        tokens := tokens + (← checkTokenRanges view index source)
        occurrences := occurrences + (← checkOccurrences index source trace)
    counts := counts ++ [(tokens, occurrences)]
  return counts

#eval show IO Unit from do
  let counts ← checkQueries [
    "CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT UNIQUE, c REAL);",
    "CREATE TABLE u(a INTEGER, d TEXT);"] [
    "SELECT a + 1, \"b\" || t.c, [a], t.a FROM t;",
    "SELECT max(a), (a) * (c + 1) FROM t;",
    "SELECT (SELECT u.d FROM u WHERE u.a = t.a), EXISTS (SELECT 1 FROM u WHERE d = b) FROM t;",
    "SELECT a IN (SELECT a FROM u WHERE d > (SELECT b FROM t)) FROM t;",
    "SELECT 1, 'a', a FROM t;",
    "SELECT t.'a' + 1, t.\"b\", `c` FROM t;"]
  -- The tokens include names that are no column or table (`max`), so one count is higher.
  unless counts == [(7, 7), (4, 3), (10, 10), (6, 6), (1, 1), (5, 5)] do
    throw <| IO.userError s!"the queries have {counts} tokens and occurrences"
