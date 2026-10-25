import Belay.Sqlite.Model.Resolution.CommonTableCopies
import Belay.Sqlite.Model.Resolution.CommonTableRecursion

set_option doc.verso true

/-! Instantiate CTE and stored-view uses as indexed derived sources. The copied parent relation
supplies each use's outer columns; name lookup uses the definition's written parent relation. -/

namespace Belay.Sqlite.Model

/-- Copy one query and its ordinary children, expanding CTE and view sources in FROM order.
The bounded walk follows the finite syntax graph; active definitions detect circular uses.
The returned local mapping also rewrites expression indexes of a surrounding write.
Entering a stored definition resets CTE lookup to its own syntax. The separate
active-view positions detect cycles across that scope boundary; copied parent indexes
still describe the use site. Early stored-syntax restrictions point at that use.
{lit}`skipped` removes recursive terms while the anchor is checked; {lit}`recursiveSource`
provides only their preparation-time output names. Such queries always end in a recursion
restriction and never supply fabricated rows to evaluation. Empty argument parentheses
on a recursive source are accepted by SQLite; nonempty arguments remain restricted because
their special preparation order is outside the supported nonrecursive forms.

The optional {lit}`initial` is the catalog of the initial database of a two-state query. A source with the schema
name {lit}`before` finds its view there, and {lit}`inInitial` says that the query is the body of such a view:
its table names that no WITH definition of the body hides read the initial catalog too, so that the copy carries the
schema name {lit}`before` and never captures a current table. A function call such as {lit}`json_each('[1]')`
is no table name: it keeps no mark, and a view with its name is looked up in the initial catalog only. The
later resolution of the copy reads a function call in the current catalog, so a call whose name is a view
of the current catalog only is the restriction {name}`RestrictionKind.initialDatabase`. An active view is its position with the
database that it is in, so equal positions of the two catalogs are not one view. -/
def copyCommonTableQuery (catalog : Catalog) (field : Nat) (initial : Option Catalog := none) (inInitial : Bool := false) :
    List Syntax.Subquery → Nat → Option Nat → Option Nat → List (Nat × CommonTableError) →
      List (Bool × Nat) → Syntax.Subquery →
      List Nat → Option (Identifier × List Identifier) → CommonTableCopyM (Syntax.Subquery × List (Nat × Nat))
  | _, 0, owner, _, _, _, _, _, _ => throw (.value (.restriction ([field] ++ owner.toList) .subqueryHere))
  | written, fuel + 1, owner, copiedOwner, active, activeViews, query, skipped, recursiveSource => do
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
        let (body, _) ← copyCommonTableQuery catalog field initial inInitial written fuel (some original) (some index) active activeViews body [] none
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
        if source.schema.isNone && source.table.sameName name then
          if source.arguments.any (!·.isEmpty) then
            throw (SourceIssue.value (.restriction
              ((if let some index := owner then [field, index] else []) ++ path) .recursiveCommonTable))
          let index ← reserveCommonTableQuery (owner.getD 0)
          fillCommonTableQuery index { commonTablePlaceholder with
            columns := columns.map fun column => .expression .null (some column) column.text
            parent := copiedOwner }
          return { mappedSource with query := some index, alias := some (source.alias.getD name), arguments := none }
      match (if source.schema.isSome then none else findCommonTable written source.table (written.length + 1) owner) with
      | none =>
        let usePath := (if let some index := owner then [field, index] else []) ++ path
        let reads := source.readsInitial || (inInitial && source.schema.isNone && source.arguments.isNone)
        let tagged := if reads then { mappedSource with schema := some Syntax.initialSchemaName } else mappedSource
        let ownCatalog : Option Catalog := if inInitial then initial else some catalog
        let lookup : Option Catalog := if reads then initial else if source.schema.isSome then none else ownCatalog
        match lookup.bind fun found => (found.findView source.table).map (found, ·) with
        | none =>
          if inInitial && source.arguments.isSome && source.schema.isNone && (catalog.findView source.table).isSome then
            throw (SourceIssue.value (.restriction usePath .initialDatabase))
          let _ ← liftM (resolveReference catalog usePath tagged (initial := initial))
          return tagged
        | some (viewCatalog, position, view) =>
          if source.arguments.isSome then
            throw (SourceIssue.value (.prepare (.view (.functionCall source.table))))
          let name := (viewCatalog[position]?.map (·.name)).getD source.table
          if activeViews.contains (reads, position) then
            throw (SourceIssue.value (.prepare (.view (.circular name))))
          let _ ← liftM (checkCommonTableSyntax field view.subqueries)
          let index ← reserveCommonTableQuery (owner.getD 0)
          let (body, _) ← fun state =>
            ((copyCommonTableQuery catalog field initial reads view.subqueries fuel none (some index) []
              ((reads, position) :: activeViews) view.query [] none).run state).mapError fun
                | .noSuchTable missing => .value (.prepare (.noSuchSource
                    (if reads then missing else ⟨bytes! "main." ++ missing.bytes⟩)))
                | .value (.restriction _ kind) => .value (.restriction usePath kind)
                | .value (.prepare error) => .value (.prepare error)
          fillCommonTableQuery index { body with parent := copiedOwner }
          modify fun state => { state with
            viewRoots := (index, name) :: state.viewRoots
            columnNames := match view.columns with
              | some names => (index, names) :: state.columnNames
              | none => state.columnNames
            viewUsePaths := ((List.range (state.queries.size - index)).map
              (fun offset => (index + offset, usePath))) ++ state.viewUsePaths }
          return { tagged with query := some index, alias := some (source.alias.getD name) }
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
        let (body, _) ← copyCommonTableQuery catalog field initial inInitial written fuel (some definitionIndex) (some index)
          ((definitionIndex, .circular definition.name) :: active) activeViews anchor recursive none
        fillCommonTableQuery index { body with parent := copiedOwner }
        nameCommonTableCopy catalog field index definition initial
        if !recursive.isEmpty then
          let (_, _, names) ← commonTableOutput catalog field index initial
          let columns := definition.columns.getD (names.map Identifier.ofString)
          let mut copiedTerms : List (CompoundOperator × Nat) := []
          for original in recursive do
            let some term := written[original]? |
              throw (SourceIssue.value (.restriction [field, original] .subqueryHere))
            let termIndex ← reserveCommonTableQuery original
            let (term, _) ← copyCommonTableQuery catalog field initial inInitial written fuel (some original) (some termIndex)
              ((definitionIndex, .repeatedReference definition.name) :: active) activeViews term []
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
      (fun index => sourceExpansion catalog field copies.queries.toList copiedOwner index copies.columnNames initial)
      (if let some index := copiedOwner then [field, index] else []) initial).mapError (copies.originalIssue field))
    if let some issue := starIssue scope query.columns then
      throw (.value (issue.under (if let some index := owner then [field, index] else [])))
    for child in children do
      let _ ← copyChild child
    return (mapped, mapping)

end Belay.Sqlite.Model
