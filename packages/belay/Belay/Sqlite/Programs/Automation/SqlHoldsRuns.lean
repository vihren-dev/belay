import Belay.Sqlite.Programs.Automation.SqlHoldsFacts

set_option doc.verso true

/-! The facts that {lit}`sql_holds` proves about the run of a subquery of a resolved claim: its rows as a term over
the rows of tables, no fault, and, when a law gives it, the end {lit}`done`. The laws are the read of one table of
the current or the initial database with row-wise expressions
({name}`Belay.Sqlite.Model.Resolved.Query.simple_subqueryRun_rowwise`) and the {lit}`EXCEPT` of two subqueries
({name}`Belay.Sqlite.Model.Resolved.Query.PlainExcept.subqueryRun`). The goals that a law leaves stay open for the
user. -/

namespace Belay.Sqlite.ClaimTactic
open Lean Meta Model

/-- The proofs about one run of a subquery: {lit}`run.rows = rows`, {lit}`run.fault = .none`, and
{lit}`run.ending = .done` when a law gives it, with the goals that the laws leave. -/
structure RunFact where
  /-- The proof of the rows. -/
  rows : Expr
  /-- The proof that the run has no fault. -/
  fault : Expr
  /-- The proof that the run ends with {lit}`done`, when a law gives it. -/
  ending : Option Expr
  /-- The goals that the laws leave. -/
  goals : Array MVarId := #[]

/-- The elements of a term that reduces to a list literal. -/
partial def listElements? (list : Expr) : MetaM (Option (List Expr)) := do
  match_expr ← whnfD list with
  | List.nil _ => return some []
  | List.cons _ head tail => return (← listElements? tail).map (head :: ·)
  | _ => return none

/-- A field of a resolved query, reduced to its head. -/
def queryField (query : Expr) (field : Name) : MetaM Expr := do
  whnfD (← mkAppM (``Resolved.Query ++ field) #[query])

/-- The fact for the run of a query that reads one table with row-wise expressions and has no other clause. -/
def simpleFact (hints : Array Expr) (query context database outer initial : Expr) : MetaM RunFact := do
  let (sources, filter, names) := (← queryField query `sources, ← queryField query `filter, ← queryField query `names)
  let some outputs ← listElements? (← queryField query `columns) | noLaw m!"the result columns of{indentExpr query}"
  let columns ← outputs.mapM fun output => do
    let_expr Resolved.Output.scalar column := ← whnfD output
      | noLaw m!"the result column{indentExpr output}\nwhich is not a scalar expression"
    return column
  let columnList ← mkListLit (mkConst ``Resolved.Expr) columns
  let simple ← mkAppM ``Resolved.Query.simple
    #[sources, filter, ← mkAppM ``List.map #[mkConst ``Resolved.Output.scalar, columnList], names]
  unless ← isDefEq query simple do noLaw (← differingPart query simple)
  let some [source] ← listElements? sources | noLaw m!"a FROM clause without exactly one source in{indentExpr query}"
  let_expr Resolved.QuerySource.mk _ from_ _ := ← whnfD source | noLaw m!"the source{indentExpr source}"
  let sourceLaw (law : Name) (raw position : Expr) (arguments : Array Expr) : MetaM Expr := do
    let (table, present) ← tableFact hints raw position
    try mkAppM law (arguments ++ #[position, table, ← mkEqRefl sources, present])
    catch _ => noLaw m!"the source{indentExpr source}\nwhich is not one table without a join condition"
  let found ← match_expr ← whnfD from_ with
    | Resolved.Source.table position =>
      sourceLaw ``Resolved.Query.source_first_from database position #[context, simple, database, initial]
    | Resolved.Source.initialTable position => do
      let_expr Option.some _ start := initial | noLaw m!"a read of the initial database in a claim without one"
      sourceLaw ``Resolved.Query.source_initialTable start position #[context, simple, database, start]
    | _ => noLaw m!"the source{indentExpr from_}"
  let rowwise (law : Name) (list : Expr) : MetaM Expr := do
    let some proof ← decidedLaw? law list
      | noLaw m!"an expression of{indentExpr (← whnfD list)}\nthat is not made of columns, literals and parameters \
        with comparisons, AND, OR, NOT and IS NULL"
    return proof
  let parameters ← whnfD (← mkAppM ``Resolved.EvalContext.parameters #[context])
  let law ← mkAppM ``Resolved.Query.simple_subqueryRun_rowwise #[context, database, outer, initial, sources, filter,
    columnList, names, parameters, found, ← mkEqRefl (mkConst ``Resolved.Fault.none), ← mkEqRefl parameters,
    ← rowwise ``Resolved.QuerySource.rowwise_of_all sources,
    ← rowwise ``Resolved.Expr.rowwise_of_all (← mkAppM ``Option.toList #[filter]),
    ← rowwise ``Resolved.Expr.rowwise_of_all columnList]
  let rest ← mkAppM ``And.right #[law]
  return { rows := ← mkAppM ``And.left #[law], fault := ← mkAppM ``And.left #[rest],
           ending := some (← mkAppM ``And.right #[rest]) }

mutual

/-- The fact for the run of subquery {lit}`index` of a context for the empty outer row: the law of the subqueries of
the statement context or of a nested context gives the run of the query at that index. -/
partial def subqueryFact (hints : Array Expr) (term : Expr) : MetaM RunFact := do
  let (equation, run, open_) ← try applyLaw hints ``Resolved.statementContext_subqueries term
    catch _ => applyLaw hints ``Resolved.subqueryContext_subqueries term
  unless open_.isEmpty do noLaw m!"the subquery{indentExpr term}"
  let fact ← runFact hints run
  let along (field : Name) (proof : Expr) : MetaM Expr := do mkEqTrans (← mkCongrArg (mkConst field) equation) proof
  return { rows := ← along ``Resolved.SubqueryRun.rows fact.rows,
           fault := ← along ``Resolved.SubqueryRun.fault fact.fault,
           ending := ← fact.ending.mapM (along ``Resolved.SubqueryRun.ending), goals := fact.goals }

/-- The fact for the run of a query of the form {name}`Resolved.Query.PlainExcept`. The goal that the rows of the
left term have no two rows that are equal but not identical stays open. -/
partial def exceptFact (hints : Array Expr) (query context database initial compound : Expr) : MetaM RunFact := do
  let_expr Resolved.Compound.mk first rest collations := ← whnfD compound | noLaw m!"the compound{indentExpr compound}"
  let some [step] ← listElements? rest | noLaw m!"a compound SELECT with more than two terms{indentExpr query}"
  let_expr Prod.mk _ _ operator later := ← whnfD step | noLaw m!"the compound{indentExpr compound}"
  unless (← whnfD operator).isConstOf ``CompoundOperator.except do noLaw m!"the compound operator {operator}"
  let shape ← mkFreshExprMVar (← mkAppM ``Resolved.Query.PlainExcept #[query, first, later, collations])
  for part in ← shape.mvarId!.constructor do
    try part.refl catch _ => noLaw m!"{(queryParts.lookup (← part.getTag)).getD (toString (← part.getTag))} \
      in the EXCEPT query{indentExpr query}"
  let empty ← mkListLit (mkConst ``Value) []
  let left ← subqueryFact hints (← mkAppM ``Resolved.EvalContext.subqueries #[context, first, empty])
  let right ← subqueryFact hints (← mkAppM ``Resolved.EvalContext.subqueries #[context, later, empty])
  let (some leftDone, some rightDone) := (left.ending, right.ending)
    | noLaw m!"a term of the EXCEPT query{indentExpr query}\nwhose end is not known"
  let_expr Eq _ _ leftRows := ← inferType left.rows | noLaw m!"the rows of{indentExpr query}"
  let identical ← mkFreshExprSyntheticOpaqueMVar
    (← mkEq (← mkAppM ``Resolved.equalRowsIdentical #[collations, leftRows]) (mkConst ``Bool.true)) `identical
  let law ← mkAppM ``Resolved.Query.PlainExcept.subqueryRun #[shape, context, database, initial, leftDone, rightDone,
    ← mkEqTrans (← mkCongrArg (mkApp (mkConst ``Resolved.equalRowsIdentical) collations) left.rows) identical]
  let combine := mkApp2 (mkConst ``CompoundOperator.combine) collations (mkConst ``CompoundOperator.except)
  return { rows := ← mkEqTrans (← mkAppM ``And.left #[law]) (← mkCongr (← mkCongrArg combine left.rows) right.rows),
           fault := ← mkAppM ``And.right #[law], ending := none,
           goals := left.goals ++ right.goals |>.push identical.mvarId! }

/-- The fact for the run of a resolved query in a context. -/
partial def runFact (hints : Array Expr) (run : Expr) : MetaM RunFact := do
  let_expr Resolved.Query.subqueryRun context database outer query initial := run | noLaw m!"the run{indentExpr run}"
  match_expr ← queryField query `compound with
  | Option.some _ compound => exceptFact hints query context database initial compound
  | _ => simpleFact hints query context database outer initial

end

end Belay.Sqlite.ClaimTactic
