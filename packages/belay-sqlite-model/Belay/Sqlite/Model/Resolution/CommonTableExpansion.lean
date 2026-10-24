import Belay.Sqlite.Model.Resolution.CommonTableCopies
import Belay.Sqlite.Model.Resolution.CommonTableRecursion

set_option doc.verso true

/-! Instantiate ordinary CTE uses as indexed derived sources. The copied parent relation
supplies each use's outer columns; name lookup uses the definition's written parent relation. -/

namespace Belay.Sqlite.Model

/-- Copy one query and its ordinary children, expanding named CTE sources in FROM order.
The bounded walk follows the finite syntax graph; active definitions detect circular uses.
The returned local mapping also rewrites expression indexes of a surrounding write.
{lit}`skipped` removes recursive terms while the anchor is checked; {lit}`recursiveSource`
provides only their preparation-time output names. Such queries always end in a recursion
restriction and never supply fabricated rows to evaluation. Empty argument parentheses
on a recursive source are accepted by SQLite; nonempty arguments remain restricted because
their special preparation order is outside the supported nonrecursive forms. -/
def copyCommonTableQuery (catalog : Catalog) (field : Nat) (written : List Syntax.Subquery) :
    Nat → Option Nat → Option Nat → List (Nat × CommonTableError) → Syntax.Subquery →
      List Nat → Option (Identifier × List Identifier) → CommonTableCopyM (Syntax.Subquery × List (Nat × Nat))
  | 0, owner, _, _, _, _, _ => throw (.value (.restriction ([field] ++ owner.toList) .subqueryHere))
  | fuel + 1, owner, copiedOwner, active, query, skipped, recursiveSource => do
    let children := (List.range written.length).filter fun index =>
      (written[index]?).any fun child => child.parent == owner && child.commonTable.isNone && !skipped.contains index
    let mapping ← children.mapM fun index => do return (index, ← reserveCommonTableQuery index)
    let mapped ← liftM (reindexCommonTableQuery field owner mapping query)
    let copyChild := fun original => do
      let some index := mapping.lookup original |
        throw (SourceIssue.value (.restriction ([field] ++ owner.toList) .subqueryHere))
      unless (← get).filled.contains index do
        let some body := written[original]? |
          throw (SourceIssue.value (.restriction [field, original] .subqueryHere))
        let (body, _) ← copyCommonTableQuery catalog field written fuel (some original) (some index) active body [] none
        fillCommonTableQuery index { body with parent := copiedOwner }
      return index
    let copySource := fun (path : List Nat) (source : Syntax.TableReference) => do
      let mappedSource ← liftM (source.reindexM fun index => match mapping.lookup index with
        | some copied => Except.ok copied
        | none => Except.error (SourceIssue.value (.restriction ([field] ++ owner.toList) .subqueryHere)))
      if let some child := source.query then
        let _ ← copyChild child
        return mappedSource
      if let some (name, columns) := recursiveSource then
        if source.table.sameName name then
          if source.arguments.any (!·.isEmpty) then
            throw (SourceIssue.value (.restriction
              ((if let some index := owner then [field, index] else []) ++ path) .recursiveCommonTable))
          let index ← reserveCommonTableQuery (owner.getD 0)
          fillCommonTableQuery index { commonTablePlaceholder with
            columns := columns.map fun column => .expression .null (some column) column.text
            parent := copiedOwner }
          return { mappedSource with query := some index, alias := some (source.alias.getD name), arguments := none }
      match findCommonTable written source.table (written.length + 1) owner with
      | none =>
        let _ ← liftM (resolveReference catalog ((if let some index := owner then [field, index] else []) ++ path) mappedSource)
        return mappedSource
      | some definitionIndex =>
        let some body := written[definitionIndex]? |
          throw (SourceIssue.value (.restriction [field, definitionIndex] .subqueryHere))
        let some definition := body.commonTable |
          throw (SourceIssue.value (.restriction [field, definitionIndex] .subqueryHere))
        if let some error := active.lookup definitionIndex then
          throw (SourceIssue.value (.prepare (.commonTable error)))
        if source.arguments.isSome then
          throw (SourceIssue.value (.prepare (.commonTable (.functionCall source.table))))
        let recursiveOperator := ((body.compound.bind fun compound => compound.rest.getLast?).map Prod.fst).getD .unionAll
        let (anchor, recursive) ← liftM ((commonTableRecursiveTerms written definition body).mapError
          (fun error => SourceIssue.value (.prepare (.commonTable error))))
        let index ← reserveCommonTableQuery definitionIndex
        let (body, _) ← copyCommonTableQuery catalog field written fuel (some definitionIndex) (some index)
          ((definitionIndex, .circular definition.name) :: active) anchor recursive none
        fillCommonTableQuery index { body with parent := copiedOwner }
        nameCommonTableCopy catalog field index definition
        if !recursive.isEmpty then
          let (_, _, names) ← commonTableOutput catalog field index
          let columns := definition.columns.getD (names.map Identifier.ofString)
          let mut copiedTerms : List (CompoundOperator × Nat) := []
          for original in recursive do
            let some term := written[original]? |
              throw (SourceIssue.value (.restriction [field, original] .subqueryHere))
            let termIndex ← reserveCommonTableQuery original
            let (term, _) ← copyCommonTableQuery catalog field written fuel (some original) (some termIndex)
              ((definitionIndex, .repeatedReference definition.name) :: active) term []
              (some (definition.name, columns))
            fillCommonTableQuery termIndex { term with parent := some index }
            copiedTerms := (recursiveOperator, termIndex) :: copiedTerms
          let completed : Syntax.Subquery := { body with compound := body.compound.map fun (compound : Syntax.Compound) =>
            { compound with rest := compound.rest ++ copiedTerms } }
          modify fun state => { state with
            queries := state.queries.set! index { completed with parent := copiedOwner }
            recursive := state.recursive ++ [(index, copiedTerms.map Prod.snd)] }
        return { mappedSource with query := some index, alias := some (source.alias.getD definition.name) }
    if let some compound := query.compound then
      for child in compound.terms.reverse do
        let _ ← copyChild child
    let source ← query.source.mapM (copySource [1])
    let joins ← (query.joins.zip mapped.joins).zipIdx.mapM fun ((original, mapped), position) => do
      return { mapped with source := ← copySource [2, position, 1] original.source }
    let mapped := { mapped with source, joins }
    let copies ← get
    let (_, scope) ← liftM ((resolveSources catalog source joins 0
      (fun index => sourceExpansion catalog field copies.queries.toList copiedOwner index copies.columnNames)
      (if let some index := copiedOwner then [field, index] else [])).mapError (copies.originalIssue field))
    if let some issue := starIssue scope query.columns then
      throw (.value (issue.under (if let some index := owner then [field, index] else [])))
    for child in children do
      let _ ← copyChild child
    return (mapped, mapping)

/-- A statement's ordinary queries after per-use CTE expansion. The syntax root retains
the statement's clauses; the mapping translates the direct query references of a write. -/
structure CommonTableExpansion where
  /-- The rewritten query clauses of a SELECT, or the empty root used for a write. -/
  query : Syntax.Subquery
  /-- The complete executable query list, original paths and explicit source names. -/
  copies : CommonTableCopies
  /-- Old and new indexes of the statement's ordinary direct subqueries. -/
  rootIndexes : List (Nat × Nat)

/-- Expand WITH definitions for one statement. Unused definitions are not prepared;
duplicates and malformed parent links are checked before the used definitions are copied.
The query list without definitions is returned unchanged by the caller's fast path. -/
def expandCommonTables (catalog : Catalog) (field : Nat) (query : Syntax.Subquery)
    (written : List Syntax.Subquery) : Except SourceIssue CommonTableExpansion := do
  if let some error := duplicateCommonTable written then throw (.value (.prepare (.commonTable error)))
  for index in List.range written.length do
    if (written[index]?.bind (·.parent)).any (index ≤ ·) then
      throw (.value (.restriction [field, index] .subqueryHere))
  let ((query, rootIndexes), copies) ←
    (copyCommonTableQuery catalog field written (written.length + 1) none none [] query [] none).run {}
  if copies.filled.length != copies.queries.size then throw (.value (.restriction [field] .subqueryHere))
  return { query, copies, rootIndexes }

/-- Keep ordinary query syntax unchanged, or expand the statement's WITH definitions.
The identity branch preserves the existing query indexes and needs no new copies. -/
def prepareCommonTables (catalog : Catalog) (field : Nat) (query : Syntax.Subquery)
    (written : List Syntax.Subquery) : Except SourceIssue CommonTableExpansion :=
  if written.any (·.commonTable.isSome) then expandCommonTables catalog field query written else
    .ok {
      query
      rootIndexes := (List.range written.length).map fun index => (index, index)
      copies := { queries := written.toArray, origins := (List.range written.length).toArray } }

end Belay.Sqlite.Model
