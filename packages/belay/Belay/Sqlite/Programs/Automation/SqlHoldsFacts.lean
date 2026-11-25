import Belay.Sqlite.Programs.Automation.SqlSelectEval
import Belay.Sqlite.Programs.Claims.CatalogClaimBridge

set_option doc.verso true

/-! The steps of {lit}`sql_holds` that apply one law: instantiate the law at a term of the goal, and close the
premises that a hint or a computation closes. A premise about the catalog of a database comes from a hint
{lit}`db.HasCatalog schema`. A premise that is an equation with a term without variables on its left side is
computed by the kernel ({name}`Belay.Sqlite.Select.evaluationProof?`). Each proof that these functions build is
checked by the kernel. -/

namespace Belay.Sqlite.ClaimTactic
open Lean Meta Model

/-- Stop with a message that names the part of the claim that has no law in {lit}`sql_holds`. -/
def noLaw {α : Type} (part : MessageData) : MetaM α :=
  throwError m!"sql_holds has no law for {part}. Prove this goal with the laws of the parts, for example \
    Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists."

/-- The catalog of a raw database from the hints: a raw database without variables, and the proof that the two have
the same catalog. A hint is a proof of {lit}`db.HasCatalog schema` or of an equation of two catalogs. -/
def catalogFact (hints : Array Expr) (database : Expr) : MetaM (Expr × Expr) := do
  let catalog ← mkAppM ``Model.Database.catalog #[database]
  for hint in hints do
    let_expr Eq _ left right := ← whnfD (← inferType hint) | continue
    let_expr Model.Database.catalog schema := right | continue
    if schema.hasFVar || schema.hasMVar then continue
    if ← isDefEq left catalog then
      return (schema, ← mkExpectedTypeHint hint (← mkEq catalog right))
  throwError m!"sql_holds needs the catalog of the database{indentExpr database}\nGive a hint db.HasCatalog schema \
    or an equation of its catalog, with a schema that has no variable."

/-- The proof of the premise of a law that has the form {lit}`P subject` and that a computation decides, applied to
the law: {lit}`law subject proof`. The result is {lean}`(none : Option Expr)` when the kernel does not accept the
premise. -/
def decidedLaw? (law : Name) (subject : Expr) : MetaM (Option Expr) := do
  let premise := (← instantiateForall (← inferType (mkConst law)) #[subject]).bindingDomain!
  return (← Select.evaluationProof? premise).map (mkApp2 (mkConst law) subject)

/-- The table at a position of a raw database whose catalog a hint gives, and the proof of
{lit}`database.table position = some table`. -/
def tableFact (hints : Array Expr) (database position : Expr) : MetaM (Expr × Expr) := do
  let (schema, same) ← catalogFact hints database
  let entry ← mkAppM ``Catalog.tableAt #[← mkAppM ``Model.Database.catalog #[schema], position]
  let some present ← Select.evaluationProof? (← mkEq (← mkAppM ``Option.isSome #[entry]) (mkConst ``Bool.true))
    | noLaw m!"a source at the catalog position {position}, which has no table"
  let proof ← mkAppM ``Model.Database.table_of_sameCatalog #[same, position, present]
  let_expr Eq _ _ found := ← inferType proof | noLaw m!"the table at the catalog position {position}"
  return (found.appArg!, proof)

/-- Close a premise of the form {lit}`raw.catalog = ?schema.catalog` from the hints. -/
def catalogPremise (hints : Array Expr) (premise : Expr) : MetaM Bool := do
  let type ← instantiateMVars (← inferType premise)
  let_expr Eq _ left right := type | return false
  let_expr Model.Database.catalog database := left | return false
  unless right.isAppOf ``Model.Database.catalog && right.hasExprMVar do return false
  let (_, proof) ← catalogFact hints database
  unless ← isDefEq type (← inferType proof) do return false
  premise.mvarId!.assign proof
  return true

/-- Close an equation whose right side has a metavariable: the kernel computes the left side, unification fills
the right side with the value, and {name}`Belay.Sqlite.Select.evaluationProof?` proves the equation. A left side
with a variable is reduced only at its head, so that the terms of the variables keep their form in the goals. -/
def computedPremise (premise : Expr) : MetaM Bool := do
  let type ← instantiateMVars (← inferType premise)
  let_expr Eq _ left right := type | return false
  unless right.hasExprMVar do return false
  let saved ← saveState
  try
    if ← isDefEq right (← if left.hasFVar then whnfD left else Select.kernelNormalize left) then
      if let some proof ← Select.evaluationProof? (← instantiateMVars type) then
        premise.mvarId!.assign proof
        return true
  catch _ => pure ()
  saved.restore
  return false

/-- Instantiate a law whose conclusion is an equation or an equivalence: unify its left side with the target, and
close the premises that the hints or a computation close. The result is the proof, its right side, and the
premises that stay open, in order. -/
def applyLaw (hints : Array Expr) (law : Name) (target : Expr) : MetaM (Expr × Expr × Array Expr) := do
  let constant ← mkConstWithFreshMVarLevels law
  let (arguments, _, conclusion) ← forallMetaTelescopeReducing (← inferType constant)
  let (left, right) ← match_expr conclusion with
    | Iff left right => pure (left, right)
    | Eq _ left right => pure (left, right)
    | _ => throwError m!"sql_holds: the law {law} is not an equation or an equivalence"
  unless ← isDefEq left target do
    throwError m!"sql_holds cannot apply the law {law} to{indentExpr target}"
  let mut open_ := #[]
  for argument in arguments do
    if (← instantiateMVars argument).isMVar && (← isProp (← inferType argument)) then
      unless (← catalogPremise hints argument) || (← computedPremise argument) do
        open_ := open_.push argument
  return (mkAppN constant arguments, ← instantiateMVars right, open_)

/-- The parts of a resolved query, with the words that a message uses for each. -/
def queryParts : List (Name × String) :=
  [(`sources, "FROM"), (`filter, "WHERE"), (`aggregate, "an aggregate"), (`groupBy, "GROUP BY"),
    (`columns, "the result columns"), (`names, "the names of the result columns"), (`orderBy, "ORDER BY"),
    (`offset, "OFFSET"), (`limit, "LIMIT"),
    (`limitParameter, "LIMIT with a parameter"), (`offsetParameter, "OFFSET with a parameter"),
    (`outer, "a column of an outer query"), (`aggregates, "an aggregate"), (`having, "HAVING"),
    (`distinct, "DISTINCT"), (`compound, "a compound SELECT")]

/-- The words for the first part in which a resolved query differs from the form of a law. -/
def differingPart (query expected : Expr) : MetaM MessageData := do
  for (field, words) in queryParts do
    let projection (term : Expr) := do whnfD (← mkAppM (``Resolved.Query ++ field) #[term])
    unless ← isDefEq (← projection query) (← projection expected) do return m!"{words} in the query{indentExpr query}"
  return m!"the form of the query{indentExpr query}"

end Belay.Sqlite.ClaimTactic
