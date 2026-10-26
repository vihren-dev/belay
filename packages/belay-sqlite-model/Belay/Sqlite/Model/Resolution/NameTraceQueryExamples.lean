import Belay.Sqlite.Model.Resolution.QueryBodyArms

set_option doc.verso true

/-! Examples of the name trace of the clauses of one query: the alias of a result column and its use
in {lit}`ORDER BY`, the operand of an aggregate, the candidates of a missing {lit}`GROUP BY` name, and
the trace of a query that fails. -/

namespace Belay.Sqlite.Model.NameTraceQueryExamples

/-- The identifier of a text. -/
private def name (text : String) : Identifier := Identifier.ofString text

/-- The scope of one table {lit}`t(a INTEGER, b TEXT)`. -/
private def tableT : Scope :=
  Scope.place [{ name := name "t", columns := [{ name := name "a", declaredType := some "INTEGER" },
    { name := name "b", declaredType := some "TEXT" }] }]

/-- An unqualified column name. -/
private def identifier (text : String) : Syntax.Expr := .identifier (name text) .none

/-- Whether a result is a name bound to exactly one column. -/
private def isFoundOne : NameResult → Bool
  | .found [_] => true
  | .found _ | .ambiguous _ | .missing .. | .source _ | .schema _ | .resultColumn _ | .declares
  | .compared .. | .unreached _ => false

/-- Whether a result is a name that no column has, as SQLite's {lit}`no such column`. -/
private def isMissingError : NameResult → Bool
  | .missing .error _ => true
  | .missing .textLiteral _ | .missing .booleanKeyword _ | .missing .rowidName _ | .found _ | .ambiguous _
  | .source _ | .schema _ | .resultColumn _ | .declares | .compared .. | .unreached _ => false

/-- Whether a result is a name that no column has, with the two columns of the scope and then the
alias of the first result column as candidates. -/
private def listsAliasLast (alias : Identifier) : NameResult → Bool
  | .missing .error [.column _, .column _, last] => last == .resultAlias alias 0
  | .missing .error _ | .missing .textLiteral _ | .missing .booleanKeyword _ | .missing .rowidName _
  | .found _ | .ambiguous _ | .source _ | .schema _ | .resultColumn _ | .declares | .compared .. | .unreached _ =>
    false

/-- A query over the scope of {lit}`tableT` with the given result columns, grouping terms and ordering terms. -/
private def query (columns : List Syntax.ResultColumn) (groupBy : List Syntax.Expr := [])
    (orderBy : List Syntax.OrderTerm := []) : Syntax.Subquery :=
  { columns, source := none, joins := [], filter := none, groupBy, orderBy, limit := none, offset := none,
    parent := none }

/-- The traced resolution of the clauses of a query over {lit}`tableT`. -/
private def traced (query : Syntax.Subquery) :=
  resolveQueryBodyTraced true tableT {} [] [] query

/-- The alias of a result column is recorded after the column, and an {lit}`ORDER BY` term that names
the alias records the result column. -/
private def aliasAndOrderBy : Bool :=
  (match (traced (query [.expression (identifier "a") (some (name "x")) "a"]
      (orderBy := [{ expression := identifier "x", descending := false }]))).trace with
    | [column, alias, order] =>
      column.path == [0, 0, 0] && column.role == .columnReference &&
      alias.path == [0, 0, 1] && alias.role == .resultAlias &&
      order.path == [5, 0, 0] && order.role == .columnReference &&
      order.result == .resultColumn 0
    | _ => false)

#guard aliasAndOrderBy

/-- The operand of an aggregate is recorded at the operand of the call. -/
private def aggregateOperand : Bool :=
  (match (traced (query [.expression (.call "max" [identifier "a"]) none "max(a)"])).trace with
    | [operand] => operand.path == [0, 0, 0, 1, 0] && isFoundOne operand.result
    | _ => false)

#guard aggregateOperand

/-- A {lit}`GROUP BY` name that is no column fails, and its occurrence lists the columns and then the
aliases of the result columns as candidates. -/
private def missingGroupByName : Bool :=
  (match (traced (query [.expression (identifier "a") (some (name "x")) "a"] (groupBy := [identifier "z"]))) with
    | ⟨.error (.prepare (.noSuchColumn missing)), trace⟩ =>
      missing == name "z" &&
      (match trace.getLast? with
        | some occurrence =>
          occurrence.path == [4, 0] &&
          listsAliasLast (name "x") occurrence.result
        | none => false)
    | _ => false)

#guard missingGroupByName

/-- A query that fails keeps the trace up to and including the failing name, and none after it. -/
private def failureKeepsTrace : Bool :=
  (match traced (query [.expression (identifier "a") none "a", .expression (identifier "z") none "z",
      .expression (identifier "b") none "b"]) with
    | ⟨.error (.prepare (.noSuchColumn missing)), [first, second]⟩ =>
      missing == name "z" && first.path == [0, 0, 0] && second.path == [0, 1, 0] &&
      isMissingError second.result
    | _ => false)

#guard failureKeepsTrace

/-- A failure in the pass that lists the aggregate calls keeps the occurrences of the calls before it:
in {lit}`SELECT max(a)+1, max(z)+1`, the trace holds {lit}`a` and then the missing {lit}`z`. -/
private def failureAfterAggregateKeepsEarlierCalls : Bool :=
  (match traced (query [
      .expression (.arithmetic .add (.call "max" [identifier "a"]) (.numeric "1")) none "max(a)+1",
      .expression (.arithmetic .add (.call "max" [identifier "z"]) (.numeric "1")) none "max(z)+1"]) with
    | ⟨.error (.prepare (.noSuchColumn missing)), [first, second]⟩ =>
      missing == name "z" && first.path == [0, 0, 0, 1, 1, 0] && second.path == [0, 1, 0, 1, 1, 0] &&
      isFoundOne first.result && isMissingError second.result
    | _ => false)

#guard failureAfterAggregateKeepsEarlierCalls

end Belay.Sqlite.Model.NameTraceQueryExamples
