import Belay.Sqlite.Model.Resolution.ResultColumnTraced

set_option doc.verso true

/-! The equations of {lit}`resolveResultColumn` in the shape that the function had before the name
trace was threaded through it: the proofs of the laws about result columns unfold it with
{lit}`simp only [traced_arms]` and meet the same steps as before. -/

namespace Belay.Sqlite.Model

/-- For every scope: {lit}`*` is {lit}`no tables specified` when the query has no source with visible
columns, else it gives every visible column. Proof sketch: unfold the traced form and push the
projection through the monad. -/
@[traced_arms] theorem resolveResultColumn_star (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (column : Nat) :
    resolveResultColumn dqs scope shapes column .star =
      if !(scope.inner.any (·.namesVisible)) then throw (.prepare .noTablesSpecified) else
      scope.visible.mapM fun (position, defined) =>
        (fun (operand : Operand) => (.scalar operand.1, defined.name.text, operand.2)) <$>
          scope.starOperand position defined := by
  simp only [resolveResultColumn, resolveResultColumnTraced, traced_drop]

/-- For every qualifier: {lit}`x.*` gives the columns of source {lit}`x`. Proof sketch: unfold the traced
form and push the projection through the monad. -/
@[traced_arms] theorem resolveResultColumn_sourceStar (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (column : Nat) (source : Identifier) :
    resolveResultColumn dqs scope shapes column (.sourceStar source) = (do
      let columns ← sourceStarColumns scope source
      pure (columns.map fun ((expression, affinity), name) => (.scalar expression, name, affinity))) := by
  simp only [resolveResultColumn, resolveResultColumnTraced, sourceStarColumns, traced_drop]

/-- For every expression and alias: an aggregate call is a whole result column, any other expression
a scalar with the affinity of its operand, and the name is the alias, else the defined name, else the
text. Proof sketch: unfold the traced form, push the projection through the monad, and split on the
alias, the expression and the aggregate that its name gives. -/
@[traced_arms] theorem resolveResultColumn_expression (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (column : Nat) (value : Syntax.Expr) (alias : Option Identifier) (text : String) :
    resolveResultColumn dqs scope shapes column (.expression value alias text) = (do
    let named := fun (output : Resolved.Output) (defined : Option String) (affinity : Option Affinity) =>
      (pure [(output, (alias.map (·.text)).getD (defined.getD text), affinity)] :
        Except ValueIssue (List (Resolved.Output × String × Option Affinity)))
    let outerAggregate := fun (operand : Resolved.Expr) =>
      if operand.readsUnder shapes shapes.outer then
        throw ((ValueIssue.restriction [] .outerAggregate).under [0, column, 0])
      else (pure () : Except ValueIssue Unit)
    let scalar := fun (defined : Option String) => do
      let (resolved, affinity) ← (resolveOperand dqs scope shapes false value).mapError
        (ValueIssue.under [0, column, 0])
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
        let (resolved, _) ← (resolveOperand dqs scope shapes true operand).mapError
          (ValueIssue.under [0, column, 0, 1, 0])
        outerAggregate resolved
        if (aggregate resolved).writesJson && resolved.subtypeUndescribed then
          throw ((ValueIssue.restriction [] .jsonSubtype).under [0, column, 0, 1, 0])
        named (.aggregate ((aggregate resolved).withCollation (operand.collationIn scope))) none none
      | none => scalar none
    | .call name [first, second] => match pairAggregateNamed name with
      | some aggregate =>
        let (label, _) ← (resolveOperand dqs scope shapes true first).mapError
          (ValueIssue.under [0, column, 0, 1, 0])
        let (operand, _) ← (resolveOperand dqs scope shapes true second).mapError
          (ValueIssue.under [0, column, 0, 1, 1])
        outerAggregate (.coalesce label operand)
        if operand.subtypeUndescribed then
          throw ((ValueIssue.restriction [] .jsonSubtype).under [0, column, 0, 1, 1])
        named (.aggregate (aggregate label operand)) none none
      | none => scalar none
    | .call _ (_ :: _ :: _ :: _) | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _
    | .identifier .. | .qualified .. | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _
    | .isNull .. | .arithmetic .. | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList ..
    | .between .. | .caseOf .. | .concatenate .. | .raise .. => scalar (definedName scope value)) := by
  simp only [resolveResultColumn, resolveResultColumnTraced, resolveOperand,
    traced_drop]
  cases alias <;> cases value with
  | call name arguments =>
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    · simp [traced_drop]
    · cases named : aggregateNamed name <;> simp [named, traced_drop]
    · cases named : pairAggregateNamed name <;> simp [named, traced_drop]
    · simp [traced_drop]
  | _ => simp [traced_drop]

end Belay.Sqlite.Model
