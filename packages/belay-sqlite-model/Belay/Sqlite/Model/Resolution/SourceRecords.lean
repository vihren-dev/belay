import Belay.Sqlite.Model.Resolution.ScopeBindings
import Belay.Sqlite.Model.Resolution.SyntaxExpr

set_option doc.verso true

/-! The occurrences that the resolution of a table reference records. A table reference has the
parts of {lit}`Syntax.TableReference`: child 0 the table, 1 its alias, 2 its arguments, 3 its query and
4 its schema. The functions build the record from the facts that the resolver has already decided;
the resolver, not the record, makes the decision. -/

namespace Belay.Sqlite.Model

/-- The tables and views of the catalog as candidates for the table of a table reference, each with
its catalog position. Indexes and triggers have no place in {lit}`FROM`. -/
def Catalog.referenceCandidates (catalog : Catalog) : List Candidate :=
  catalog.zipIdx.filterMap fun (object, position) => match object.entry with
    | .table _ => some (.catalogObject .baseTable object.name position)
    | .view _ => some (.catalogObject .storedView object.name position)
    | .index _ | .trigger _ => none

/-- The occurrence of the schema of a table reference at {lit}`path`, whose result says whether it is
{lit}`before`. -/
def schemaOccurrence (path : List Nat) (schema : Identifier) : NameOccurrence :=
  { path := path ++ [4], role := .qualifier, name := some schema, result := .schema schema.isInitialSchema }

/-- The occurrence of the table of a table reference at {lit}`path`. -/
def tableOccurrence (path : List Nat) (table : Identifier) (result : NameResult) : NameOccurrence :=
  { path := path ++ [0], role := .tableReference, name := some table, result }

/-- The occurrence of the alias that a table reference declares. -/
def aliasOccurrence (path : List Nat) (alias : Identifier) : NameOccurrence :=
  { path := path ++ [1], role := .aliasDeclaration, name := some alias, result := .declares }

/-- The occurrences of the schema of a table reference, if it has one. -/
def Syntax.TableReference.schemaOccurrences (reference : Syntax.TableReference) (path : List Nat) : NameTrace :=
  reference.schema.toList.map (schemaOccurrence path)

/-- The occurrences of a table reference that the expansion of a view or of a {lit}`WITH` definition
(or a derived table) resolved to the source {lit}`ref`: the table as written, unless it is the empty
name of a derived table, and the alias as written. The expansion gives an unaliased use the name of
the table as its alias, so an alias equal to the table is no occurrence of its own. -/
def Syntax.TableReference.expandedOccurrences (reference : Syntax.TableReference) (path : List Nat)
    (ref : SourceRef) : NameTrace :=
  let named := !reference.table.bytes.isEmpty
  (if named then [tableOccurrence path reference.table (.source ref)] else []) ++
    (reference.alias.toList.filter fun alias => !(named && alias == reference.table)).map (aliasOccurrence path)

end Belay.Sqlite.Model
