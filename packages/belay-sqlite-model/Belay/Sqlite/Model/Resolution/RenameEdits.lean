import Belay.Sqlite.Model.Resolution.RewriteBody
import Belay.Sqlite.Model.Resolution.NameTraceTypes
import Belay.Sqlite.Model.Resolution.Restrictions

set_option doc.verso true

/-! Which names of a stored view or trigger a rename rewrites (ADR 0019, D4). The binding of every name is
the one that the name trace records ({lit}`resolveSelectTraced`, {lit}`resolveProgramTraced`): the rename
adds no lookup rule of its own, so it never reads a name by its spelling. A table rename rewrites the
table references and the qualifiers that name the table itself (a qualifier that names an alias stays, as
in SQLite 3.51.0). A column rename rewrites the names that are bound to the column. A name that the model
cannot rewrite with certainty, such as a column that a join merged, is a restriction, never a silent
change of another name. -/

namespace Belay.Sqlite.Model

open Syntax

/-- What a rename changes. -/
inductive RenameTarget where
  /-- The table at the catalog position. -/
  | table (position : Nat)
  /-- The column at the index in the table at the catalog position. -/
  | column (position index : Nat)
  deriving Repr, DecidableEq

/-- A rename: what it changes, the new name and the way SQLite writes it. -/
structure RenameRequest where
  /-- The table or column that is renamed. -/
  target : RenameTarget
  /-- The new name. -/
  new : Identifier
  /-- How the new name is written. -/
  style : RenameStyle

/-- What a rename does with one occurrence of a name. -/
inductive EditDecision where
  /-- The name keeps its spelling. -/
  | keep
  /-- The name is replaced. -/
  | edit (edit : NameEdit)
  /-- The model cannot say how SQLite rewrites the name. -/
  | restricted (kind : RestrictionKind)

/-- Whether the source is the table at the position itself, not a view or a derived table that reads it. -/
def SourceRef.namesTable (source : SourceRef) (position : Nat) : Bool :=
  source.kind == .baseTable && source.position == some position

/-- Whether the binding is the column at the index of the table at the position. The columns of
{lit}`NEW` and {lit}`OLD` are those of the table of the trigger; {lit}`triggerOn` tells whether that is the
table at the position. -/
def Binding.isColumnOf (binding : Binding) (position index : Nat) (triggerOn : Bool) : Bool :=
  binding.column.index == index && match binding.source.kind with
    | .baseTable => binding.source.position == some position
    | .triggerRow => triggerOn
    | .initialTable | .storedView | .commonTable | .derivedTable | .tableFunction | .proposedRow => false

/-- What the rename does with an occurrence of the trace of a view or trigger. A name inside another stored
view is not exact: that view has its own rewrite. A column bound together with another column (a join that
merged them) is a restriction. A double-quoted name that is a string literal ({name}`MissingUse.textLiteral`)
is rewritten to a single-quoted string literal, as SQLite does at every rename ({name}`NameEdit.fixQuote`). -/
def RenameRequest.decide (request : RenameRequest) (triggerOn : Bool) (occurrence : NameOccurrence) :
    EditDecision :=
  match occurrence.name with
  | none => .keep
  | some old =>
    if !occurrence.exact then .keep else
    let edit : NameEdit := { path := occurrence.path, old, new := request.new, style := request.style }
    if occurrence.result matches .missing .textLiteral _ then .edit { edit with new := old, fixQuote := true } else
    match request.target with
    | .table position => match occurrence.result with
      | .source source => match occurrence.role with
        | .tableReference => if source.namesTable position then .edit edit else .keep
        | .qualifier => if source.namesTable position && !source.aliased then .edit edit else .keep
        | .columnReference | .columnTarget | .aliasDeclaration | .resultAlias | .comparisonSite => .keep
      | .found _ | .ambiguous _ | .missing .. | .schema _ | .resultColumn _ | .declares | .compared ..
      | .unreached _ => .keep
    | .column position index => match occurrence.result with
      | .found bindings => match occurrence.role with
        | .columnReference | .columnTarget =>
          if bindings.any (·.isColumnOf position index triggerOn) then
            if bindings.length == 1 then .edit edit else .restricted .alterRename
          else .keep
        | .tableReference | .qualifier | .aliasDeclaration | .resultAlias | .comparisonSite => .keep
      | .source _ | .ambiguous _ | .missing .. | .schema _ | .resultColumn _ | .declares | .compared ..
      | .unreached _ => .keep

/-- The edits of the rename for a trace, or the restriction of the first name that the model cannot rewrite. -/
def RenameRequest.edits (request : RenameRequest) (triggerOn : Bool) (trace : NameTrace) :
    Except RestrictionKind (List NameEdit) :=
  trace.foldlM (init := []) fun edits occurrence => match request.decide triggerOn occurrence with
    | .keep => pure edits
    | .edit edit => pure (edits ++ [edit])
    | .restricted kind => throw kind

/-- The view with every edit applied, or none when an edit leads to no name (a path the rewrite does not know). -/
def CatalogView.renameAll (view : CatalogView) (edits : List NameEdit) : Option CatalogView := do
  let (query, subqueries) ← edits.foldlM (init := (view.query, view.subqueries)) fun (query, subqueries) edit =>
    renameSelectAt edit query subqueries
  pure { view with query, subqueries }

/-- The trigger with every edit applied, or none when an edit leads to no name. -/
def CatalogTrigger.renameAll (trigger : CatalogTrigger) (edits : List NameEdit) : Option CatalogTrigger :=
  edits.foldlM (init := trigger) fun trigger edit => trigger.renameAt edit edit.path

end Belay.Sqlite.Model
