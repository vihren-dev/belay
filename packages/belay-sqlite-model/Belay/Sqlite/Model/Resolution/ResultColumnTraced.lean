import Belay.Sqlite.Model.Resolution.StatementCatalog
import Belay.Sqlite.Model.Resolution.SourceList
import Belay.Sqlite.Model.Resolution.QueryTerms
import Belay.Sqlite.Model.Resolution.QueryAggregates

set_option doc.verso true

/-! The result columns of a query with the name trace (ADR 0012, slice 1): the names of an
expression, the qualifier of {lit}`x.*` and the alias that a column declares are recorded where
the resolver decides them. The paths of the columns are {lit}`[0, column, part]`: part 0 is the
expression or the qualifier and part 1 the alias. -/

namespace Belay.Sqlite.Model

/-- The occurrence trace of one resolved result column with its names and the affinity of each:
{lit}`*` gives every
column of every source of the query's own sources that is not merged ({name}`Scope.visible`)
under its defined name, a merged pair as its unqualified name ({name}`Scope.starOperand`),
{lit}`x.*` every column of source {lit}`x` ({name}`sourceStarColumns`); an aggregate is a whole
result column, without affinity; any other expression is a scalar with the affinity of its
operand. A name is the {lit}`AS` alias, else the defined name of a referenced column
({name}`definedName`), else the source text as written. The alias is recorded after its
expression resolved. -/
def resolveResultColumnTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (column : Nat) :
    Syntax.ResultColumn → Traced ValueIssue (List (Resolved.Output × String × Option Affinity))
  | .star => if !(scope.inner.any (·.namesVisible)) then throw (.prepare .noTablesSpecified) else
      Traced.lift (scope.visible.mapM fun (position, defined) =>
        (fun (operand : Operand) => (.scalar operand.1, defined.name.text, operand.2)) <$> scope.starOperand position defined)
  | .sourceStar source => do
    let columns ← (sourceStarColumnsTraced scope source).underTrace [0, column, 0]
    pure (columns.map fun ((expression, affinity), name) => (.scalar expression, name, affinity))
  | .expression value alias text => do
    let named := fun (output : Resolved.Output) (defined : Option String) (affinity : Option Affinity) => do
      if let some declared := alias then Traced.record (resultAliasOccurrence column declared)
      pure [(output, (alias.map (·.text)).getD (defined.getD text), affinity)]
    let outerAggregate := fun (operand : Resolved.Expr) =>
      if operand.readsUnder shapes shapes.outer then throw ((ValueIssue.restriction [] .outerAggregate).under [0, column, 0])
      else pure ()
    let scalar := fun (defined : Option String) => do
      let (resolved, affinity) ← (resolveOperandTraced dqs scope shapes false value).under [0, column, 0]
      named (.scalar resolved) defined affinity
    match value with
    | .callStar name =>
      if normalizeIdentifier name == "count" then named (.aggregate .countRows) none none
      else throw ((starCallIssue name).under [0, column, 0])
    | .call name [] =>
      if normalizeIdentifier name == "count" then named (.aggregate .countRows) none none
      else scalar none
    | .call name [operand] => match aggregateNamed name with
      | some aggregate =>
        let (resolved, _) ← (resolveOperandTraced dqs scope shapes true operand).under [0, column, 0, 1, 0]
        outerAggregate resolved
        if (aggregate resolved).writesJson && resolved.subtypeUndescribed then
          throw ((ValueIssue.restriction [] .jsonSubtype).under [0, column, 0, 1, 0])
        named (.aggregate ((aggregate resolved).withCollation (operand.collationIn scope))) none none
      | none => scalar none
    | .call name [first, second] => match pairAggregateNamed name with
      | some aggregate =>
        let (label, _) ← (resolveOperandTraced dqs scope shapes true first).under [0, column, 0, 1, 0]
        let (operand, _) ← (resolveOperandTraced dqs scope shapes true second).under [0, column, 0, 1, 1]
        outerAggregate (.coalesce label operand)
        if operand.subtypeUndescribed then throw ((ValueIssue.restriction [] .jsonSubtype).under [0, column, 0, 1, 1])
        named (.aggregate (aggregate label operand)) none none
      | none => scalar none
    | .call _ (_ :: _ :: _ :: _) | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _
    | .identifier .. | .qualified .. | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _
    | .isNull .. | .arithmetic .. | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList ..
    | .between .. | .caseOf .. | .concatenate .. | .raise .. => scalar (definedName scope value)

/-- One resolved result column with its names and affinities: {name}`resolveResultColumnTraced`
without its trace. -/
def resolveResultColumn (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (column : Nat)
    (written : Syntax.ResultColumn) : Except ValueIssue (List (Resolved.Output × String × Option Affinity)) :=
  (resolveResultColumnTraced dqs scope shapes column written).drop

/-- The aliases of the result columns as written, one for each output: none for each column
of {lit}`*` and {lit}`x.*`. -/
def resultAliases (scope : Scope) (results : List Syntax.ResultColumn) : List (Option Identifier) :=
  results.flatMap fun
    | .star => scope.visible.map fun _ => none
    | .sourceStar name => ((scope.starColumns? name).map (·.map fun _ => none)).getD []
    | .expression _ alias _ => [alias]

end Belay.Sqlite.Model
