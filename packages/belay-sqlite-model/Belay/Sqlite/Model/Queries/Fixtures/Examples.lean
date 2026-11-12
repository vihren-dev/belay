import Belay.Sqlite.Model.Queries.Preparation.SchemaScript
import Belay.Sqlite.Model.Queries.Preparation.Messages
import Belay.Sqlite.Model.Shared.Resolved.Profile

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.Examples

open Belay.Sqlite.Model Syntax

/-- The pinned profile, SQLite 3.51.0 with its documented default limits. -/
def defaults : Profile := Profile.pinned

/-- The same release with the column limit lowered to 3, so a constant limit fails. -/
def lowered : Profile := { defaults with limits := { defaults.limits with columns := 3 } }

/-- An index key term of a column name, without sort order. -/
def key (name : Identifier) : OrderTerm := { expression := .identifier name .none, descending := false }

/-- A column definition without constraints. -/
def column (name : Identifier) (declaredType : Option String := some "TEXT") : ColumnDefinition :=
  { name, declaredType, constraints := [] }

/-- The statements of a resolution, or the empty list for a restriction. -/
def statements : ResolveResult → List Resolved.Statement
  | .resolved statements _ => statements
  | .restricted _ => []

/-- The catalog after a resolution, or the empty catalog for a restriction. -/
def catalogOf : ResolveResult → Catalog
  | .resolved _ catalog => catalog
  | .restricted _ => []

/-- Whether the resolution is a model restriction. -/
def restricted : ResolveResult → Bool
  | .restricted _ => true
  | .resolved .. => false

/-- The reason of a model restriction, or the empty text for a resolution. -/
def reason : ResolveResult → String
  | .restricted restriction => restriction.reason
  | .resolved .. => ""

-- Affinity rules in documented order; "CHARINT" and "FLOATING POINT" contain INT.
#guard [some "CHARINT", some "FLOATING POINT", some "VARCHAR(10)", some "DOUBLE", none,
  some "real blob", some "DECIMAL"].map affinityOf == [.integer, .integer, .text, .real, .blob, .blob, .numeric]

/-- Column {lit}`a` with one column constraint and no declared type. -/
def constrained (constraint : ColumnConstraint) : ColumnDefinition :=
  { name := (name! "a"), declaredType := none, constraints := [constraint] }

#guard (ExprError.valueCount (name! "t") 2 1).message == "table t has 2 columns but 1 values were supplied"

end Belay.Sqlite.Model.Resolution.Examples
