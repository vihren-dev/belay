import Belay.Sqlite.Model.Resolution.TriggerBodies

set_option doc.verso true

/-! Resolution of the statements of a trigger's body (ADR 0018, D5), one statement at a time, with
the names that the resolution decided. Each statement is resolved with the resolver of the
statement of the same name over the trigger's rows ({name}`Belay.Sqlite.Model.TriggerRow`). The
trace of a statement is relative to the statement as written; the trace of a whole trigger
({lit}`resolveProgramTraced`) places it below the statement's place in the trigger. -/

namespace Belay.Sqlite.Model

/-- The outcome of a traced computation changed as a whole, with the trace kept. -/
def Traced.mapResult {ε ε' α β : Type} (change : Except ε α → Except ε' β) (computation : Traced ε α) :
    Traced ε' β :=
  ⟨change computation.drop, computation.trace⟩

/-- The step of a raising SELECT from the step of its query: a prepare error stays, the filter and
the arms of the column make the raise, and a query that the model does not evaluate
({name}`raiseQueryPlain`) is the restriction of a {lit}`RAISE` form. -/
def raiseSelectStep (kinds : List (Option Syntax.RaiseKind)) :
    Except NodeRestriction (Except PrepareError Resolved.Step) →
      Except NodeRestriction (Except PrepareError Resolved.Step)
  | .error restriction => .error restriction
  | .ok (.error error) => .ok (.error error)
  | .ok (.ok (.query resolved subqueries)) =>
    if !raiseQueryPlain resolved subqueries then .error (triggerRestriction .raiseForm)
    else match resolved.columns.head? with
      | some (.scalar (.scalar .iif arguments)) =>
        let (arms, otherwise) := raiseArms arguments.toList kinds
        .ok (.ok (.raise resolved.filter arms otherwise))
      | some (.scalar _) | some (.aggregate _) | none => .ok (.ok (.raise resolved.filter [] kinds.head?.join))
  | .ok (.ok (.insert ..)) | .ok (.ok (.update ..)) | .ok (.ok (.delete ..)) | .ok (.ok (.raise ..)) =>
    .error (triggerRestriction .triggerForm)

/-- Resolve a SELECT whose one result column raises ({name}`raisingColumn`): the SELECT with the
column whose {lit}`RAISE` results are NULL and a column for each message, which resolves the
messages for their errors; then its filter and the arms of the column ({name}`raiseSelectStep`). A SELECT of another shape
is the restriction of a {lit}`RAISE` form. The column keeps the place of the written column and the operands of its
{lit}`CASE` keep their places, so the names of the trace are at their written paths; the messages
are text. -/
def resolveRaiseSelectTraced (context : ResolveContext) (catalog : Catalog) (row : TriggerRow)
    (query : Syntax.Subquery) (column : Syntax.Expr) (kinds : List (Option Syntax.RaiseKind))
    (messages : List Syntax.Expr) : Traced NodeRestriction (Except PrepareError Resolved.Step) :=
  let extra := messages.map fun message => Syntax.ResultColumn.expression message none ""
  Traced.mapResult (raiseSelectStep kinds)
    (bodyStepTraced (resolveBodySelectTraced context catalog row
      { query with columns := .expression column none "" :: extra } []))

/-- The step of a raising SELECT: {name}`resolveRaiseSelectTraced` without its trace. -/
def resolveRaiseSelect (context : ResolveContext) (catalog : Catalog) (row : TriggerRow)
    (query : Syntax.Subquery) (column : Syntax.Expr) (kinds : List (Option Syntax.RaiseKind))
    (messages : List Syntax.Expr) : Except NodeRestriction (Except PrepareError Resolved.Step) :=
  (resolveRaiseSelectTraced context catalog row query column kinds messages).drop

/-- The step of a write in a body whose target is a view. SQLite reads the view's query with the
rows of the trigger in sight, so a column that the model cannot find, such as {lit}`new.a`, may be
a column that SQLite finds: that is the restriction {name}`RestrictionKind.viewBodyCheck`. Any other
failed read is the error of the read, and a readable view is the error
{name}`PrepareError.viewModify`. The parse error of rows of different widths comes first. -/
def viewBodyWrite (context : ResolveContext) (catalog : Catalog) (view : Identifier) (rowsDiffer : Bool) :
    Except NodeRestriction (Except PrepareError Resolved.Step) :=
  if rowsDiffer then .ok (.error (.expression .valuesDiffer))
  else match viewColumns context catalog view with
    | .ok _ => .ok (.error (.viewModify (viewCatalogName catalog view)))
    | .error (.value (.prepare error)) => match error.viewReadClass with
      | .column => .error (triggerRestriction .viewBodyCheck)
      | .found | .later | .width _ => .ok (.error (.expression error))
    | .error (.noSuchTable name) => .ok (.error (.noSuchTable name))
    | .error (.value (.restriction path kind)) => .error { path, kind }

/-- Resolve one statement of a trigger's body over the catalog, with
the trigger's rows: an INSERT around no table, with {lit}`ON CONFLICT DO UPDATE` the restriction
of a trigger form; an UPDATE and a DELETE around the written table; a SELECT whose one result
column raises as {name}`resolveRaiseSelectTraced`, when it has no other clause than {lit}`WHERE`, and
the restriction of a {lit}`RAISE` form when it has one; and another SELECT as
{name}`resolveBodySelectTraced`. Nested WITH definitions and stored views in expression subqueries use the
same expansion as ordinary statements, retaining trigger-cell positions. The trace holds the
names that were decided, at the paths of the statement of the same name: the fields of
{lit}`Statement.insert`, {lit}`Statement.update`, {lit}`Statement.delete` and {lit}`Statement.select`,
although a body statement has no {lit}`RETURNING` and no compound. A write to a view decides no
name, because the write is a prepare error. -/
def resolveBodyStatementTraced (context : ResolveContext) (catalog : Catalog) (row : TriggerRow) :
    Syntax.BodyStatement → Traced NodeRestriction (Except PrepareError Resolved.Step)
  | .insert table columns rows conflicts algorithm subqueries =>
    if conflicts.any (·.action matches .update ..) then Traced.lift (.error (triggerRestriction .triggerForm))
    else if (catalog.findView table).isSome then
      Traced.lift (viewBodyWrite context catalog table (rows.any fun row => row.length != (rows.head?.map List.length).getD 0))
    else bodyStepTraced (resolveCommonTableWriteTraced context catalog 6 table (fun _ => row.scope 0) subqueries
      fun index resolved shapes => resolveInsertTraced context catalog table columns
        (rows.map (List.map (Syntax.Expr.reindex index))) conflicts algorithm [] resolved shapes (some row))
  | .update table assignments filter subqueries =>
    if (catalog.findView table).isSome then Traced.lift (viewBodyWrite context catalog table false) else
    bodyStepTraced (resolveCommonTableWriteTraced context catalog 4 table
      (fun shape => writtenScope table shape ++ row.scope shape.columns.length) subqueries
      fun index resolved shapes => resolveUpdateTraced context catalog table
        (assignments.map fun (name, value) => (name, value.reindex index))
        (filter.map (Syntax.Expr.reindex index)) [] resolved shapes (some row))
  | .delete table filter subqueries =>
    if (catalog.findView table).isSome then Traced.lift (viewBodyWrite context catalog table false) else
    bodyStepTraced (resolveCommonTableWriteTraced context catalog 3 table
      (fun shape => writtenScope table shape ++ row.scope shape.columns.length) subqueries
      fun index resolved shapes => resolveDeleteTraced context catalog table
        (filter.map (Syntax.Expr.reindex index)) [] resolved shapes (some row))
  | .select columns source joins filter groupBy orderBy limit offset subqueries having distinct =>
    let query : Syntax.Subquery := { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none,
                                     having, distinct }
    match columns with
    | [.expression value _ _] => match raisingColumn value with
      | some (column, kinds, messages) =>
        if source.isSome || !joins.isEmpty || !groupBy.isEmpty || !orderBy.isEmpty || limit.isSome || offset.isSome ||
            !subqueries.isEmpty || having.isSome || distinct then Traced.lift (.error (triggerRestriction .raiseForm))
        else resolveRaiseSelectTraced context catalog row query column kinds messages
      | none => bodyStepTraced (resolveBodySelectTraced context catalog row query subqueries)
    | [] | [.star] | [.sourceStar _] | _ :: _ :: _ =>
      bodyStepTraced (resolveBodySelectTraced context catalog row query subqueries)

/-- Resolve one statement of a trigger's body: {name}`resolveBodyStatementTraced` without its trace. -/
def resolveBodyStatement (context : ResolveContext) (catalog : Catalog) (row : TriggerRow)
    (statement : Syntax.BodyStatement) : Except NodeRestriction (Except PrepareError Resolved.Step) :=
  (resolveBodyStatementTraced context catalog row statement).drop

end Belay.Sqlite.Model
