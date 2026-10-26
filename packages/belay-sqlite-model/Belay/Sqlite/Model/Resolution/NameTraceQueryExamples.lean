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
      (match order.result with | .resultColumn 0 => true | _ => false)
    | _ => false)

#guard aliasAndOrderBy

/-- The operand of an aggregate is recorded at the operand of the call. -/
private def aggregateOperand : Bool :=
  (match (traced (query [.expression (.call "max" [identifier "a"]) none "max(a)"])).trace with
    | [operand] => operand.path == [0, 0, 0, 1, 0] && (match operand.result with | .found [_] => true | _ => false)
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
          (match occurrence.result with
            | .missing .error [.column _, .column _, .resultAlias alias 0] => alias == name "x"
            | _ => false)
        | none => false)
    | _ => false)

#guard missingGroupByName

/-- A query that fails keeps the trace up to and including the failing name, and none after it. -/
private def failureKeepsTrace : Bool :=
  (match traced (query [.expression (identifier "a") none "a", .expression (identifier "z") none "z",
      .expression (identifier "b") none "b"]) with
    | ⟨.error (.prepare (.noSuchColumn missing)), [first, second]⟩ =>
      missing == name "z" && first.path == [0, 0, 0] && second.path == [0, 1, 0] &&
      (match second.result with | .missing .error _ => true | _ => false)
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
      (match first.result with | .found [_] => true | _ => false) &&
      (match second.result with | .missing .error _ => true | _ => false)
    | _ => false)

#guard failureAfterAggregateKeepsEarlierCalls

end Belay.Sqlite.Model.NameTraceQueryExamples
