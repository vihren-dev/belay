import Belay.Sqlite.Codec

set_option doc.verso true

/-! JSON transport of statement syntax: the derived instances of its types, the table options
with {lit}`strict` only for a {lit}`STRICT` table, and statements with {lit}`subqueries` only
for a statement with subqueries, so that the records of earlier statements keep their form. -/

namespace Belay.Sqlite

deriving instance Lean.FromJson, Lean.ToJson for Comparison, ArithmeticOperator
deriving instance Lean.FromJson, Lean.ToJson for ConflictAlgorithm
deriving instance Lean.FromJson, Lean.ToJson for Syntax.QuoteKind
deriving instance Lean.FromJson, Lean.ToJson for Syntax.ForeignKeyAction
deriving instance Lean.FromJson, Lean.ToJson for Syntax.Expr, Syntax.DefaultExpression, Syntax.ColumnConstraint
deriving instance Lean.FromJson, Lean.ToJson for Syntax.ResultColumn, Syntax.OrderTerm
deriving instance Lean.FromJson, Lean.ToJson for Syntax.ColumnDefinition, Syntax.TableConstraint
deriving instance Lean.FromJson, Lean.ToJson for Syntax.TableReference, Syntax.Join
deriving instance Lean.FromJson, Lean.ToJson for Syntax.Subquery
deriving instance Lean.FromJson, Lean.ToJson for Syntax.ConflictAction, Syntax.ConflictClause
/-- The table options as JSON, with {lit}`strict` only for a {lit}`STRICT` table, so the
records of other tables keep their form. -/
instance : Lean.ToJson Syntax.TableOptions where
  toJson options := Lean.Json.mkObj ([("withoutRowid", Lean.toJson options.withoutRowid)] ++
    (if options.strict then [("strict", Lean.toJson true)] else []))

/-- Read the table options ({name}`Syntax.TableOptions`); a missing {lit}`strict` is a table
that is not {lit}`STRICT`. -/
instance : Lean.FromJson Syntax.TableOptions where
  fromJson? json := do
    let strict : Bool := (json.getObjValAs? Bool "strict").toOption.getD false
    return { withoutRowid := ← json.getObjValAs? Bool "withoutRowid", strict }
deriving instance Lean.FromJson, Lean.ToJson for Syntax.Statement

/-- The derived reader of a statement, which needs every field. -/
def Syntax.Statement.derivedFromJson : Lean.FromJson Syntax.Statement := inferInstance

/-- The JSON names of the statement constructors with a {lit}`subqueries` field, which the
frontend writes only for a statement with subqueries, so the records of other statements keep
the form that they had before subqueries were modeled. -/
def Syntax.Statement.subqueryConstructors : List String := ["select", "insert", "update", "delete"]

/-- The JSON of a statement with an empty {lit}`subqueries` list added to the object of one of
{name}`Syntax.Statement.subqueryConstructors` that has none. Any other JSON stays as it is, so
the derived reader reports its own error for it. -/
def Syntax.Statement.withSubqueryField (json : Lean.Json) : Lean.Json :=
  Syntax.Statement.subqueryConstructors.foldl (fun json key => match json, json.getObjVal? key with
    | .obj outer, .ok (.obj fields) => match fields.get? "subqueries" with
      | some _ => json
      | none => .obj (outer.insert key (.obj (fields.insert "subqueries" (Lean.Json.arr #[]))))
    | _, _ => json) json

/-- The derived writer of a statement, which writes every field. -/
def Syntax.Statement.derivedToJson : Lean.ToJson Syntax.Statement := inferInstance

/-- The JSON of a statement without an empty {lit}`subqueries` list, the form that the
frontend writes ({name}`Syntax.Statement.withSubqueryField` reads it back). -/
def Syntax.Statement.withoutEmptySubqueries (json : Lean.Json) : Lean.Json :=
  Syntax.Statement.subqueryConstructors.foldl (fun json key => match json, json.getObjVal? key with
    | .obj outer, .ok (.obj fields) => match fields.get? "subqueries" with
      | some (Lean.Json.arr #[]) => .obj (outer.insert key (.obj (fields.erase "subqueries")))
      | _ => json
    | _, _ => json) json

/-- Write a statement ({name}`Syntax.Statement.derivedToJson`) without an empty
{lit}`subqueries` list ({name}`Syntax.Statement.withoutEmptySubqueries`). -/
instance (priority := high) : Lean.ToJson Syntax.Statement where
  toJson statement := Syntax.Statement.withoutEmptySubqueries (Syntax.Statement.derivedToJson.toJson statement)

/-- Read a statement ({name}`Syntax.Statement.derivedFromJson`), with a missing
{lit}`subqueries` list read as empty ({name}`Syntax.Statement.withSubqueryField`). -/
instance (priority := high) : Lean.FromJson Syntax.Statement where
  fromJson? json := Syntax.Statement.derivedFromJson.fromJson? (Syntax.Statement.withSubqueryField json)

end Belay.Sqlite
