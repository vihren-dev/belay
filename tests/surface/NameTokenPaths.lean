import Belay

/-! A fixture of `tests/surface_name_tokens_test.py`: the name tokens that the translation records
in the source text of a result column (`Syntax.SourceText`, `Syntax.NameToken`) stand where the
name trace puts the names. For each token, the range that the statement's `Span.select` gives for
its path is the token's bytes in the text of the column. For each exact occurrence of the trace
that lies in a result column, the column has a token with the path of the occurrence. The
statements cover names of the expression itself, qualified and quoted names, and the names of
subqueries inside the column. The file fails to elaborate when a check fails. -/

open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Translation

/-- The statements of the SQL with the default release's grammar; a refusal fails the check. -/
def translated (text : String) : IO (Array (Located Syntax.Statement)) := do
  let grammar ← IO.ofExcept ((selectGrammar (← loadedMetadata) Release.default).mapError IO.userError)
  match ← translate grammar text.toUTF8 with
  | .ok items => return items.map (·.statement)
  | .error refusal => throw <| IO.userError s!"the translation refuses {text}: {refusal.message}"

/-- The result columns of a SELECT statement and its subqueries' names for the check. -/
def selectColumns : Syntax.Statement → List Syntax.ResultColumn
  | .select columns _ _ _ _ _ _ _ _ _ _ _ => columns
  | _ => []

/-- Fail unless the tokens of the column at `column` stand at the ranges of their paths; give the
number of tokens checked. -/
def checkTokenRanges (item : Located Syntax.Statement) (column : Nat) (source : Syntax.SourceText) : IO Nat := do
  let (textStart, _) := item.span.select [0, column, 2]
  for token in source.tokens do
    for tokenPath in token.paths do
      let path := match token.subquery with
        | none => [0, column, 0] ++ tokenPath
        | some index => [8, index] ++ tokenPath
      let found := item.span.select path
      unless found == (textStart + token.start, textStart + token.stop) do
        throw <| IO.userError s!"token {repr token} selects {found} by {path}, not the range in the text"
  return source.tokens.length

/-- Fail unless each exact occurrence with a name inside the column at `column` has a token with its
path; give the number of occurrences checked. -/
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

/-- Resolve the statements one after the other, each translated alone, and check the tokens of the
columns of each SELECT; give the numbers of tokens and of occurrences checked in each. -/
def checkScript (statements : List String) : IO (List (Nat × Nat)) := do
  let mut state : ResolveState := { catalog := [] }
  let mut counts := []
  for text in statements do
    let #[item] ← translated text | throw <| IO.userError s!"expected one statement in {text}"
    let (result, trace) := resolveStatementTraced { profile := Profile.pinned, mode := .execution } state item.value
    let mut tokens := 0
    let mut occurrences := 0
    for (column, index) in (selectColumns item.value).zipIdx do
      if let .expression _ _ source := column then
        tokens := tokens + (← checkTokenRanges item index source)
        occurrences := occurrences + (← checkOccurrences index source trace)
    counts := counts ++ [(tokens, occurrences)]
    match result with
    | .ok (_, next) => state := next
    | .error _ => pure ()
  return counts

#eval show IO Unit from do
  let counts ← checkScript [
    "CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT UNIQUE, c REAL);",
    "CREATE TABLE u(a INTEGER, d TEXT);",
    "SELECT a + 1, \"b\" || t.c, [a], t.a FROM t;",
    "SELECT max(a), (a) * (c + 1) FROM t;",
    "SELECT (SELECT u.d FROM u WHERE u.a = t.a), EXISTS (SELECT 1 FROM u WHERE d = b) FROM t;",
    "SELECT a IN (SELECT a FROM u WHERE d > (SELECT b FROM t)) FROM t;",
    "SELECT 1, 'a', a FROM t;"]
  -- The tokens include names that are no column or table (`max`, `IN`), so some counts are higher.
  unless counts == [(0, 0), (0, 0), (7, 7), (4, 3), (10, 10), (7, 6), (1, 1)] do
    throw <| IO.userError s!"the statements have {counts} tokens and occurrences"
