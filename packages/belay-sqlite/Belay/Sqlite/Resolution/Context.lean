import Belay.Sqlite.Resolution.Defaults

set_option doc.verso true

/-! The inputs of statement resolution, the result of one statement, and the
predicates on names and constraints that several statements share. -/

namespace Belay.Sqlite

/-- Whether the statements only describe a catalog, or are statements that the
execution semantics runs. A description, such as the schema text that SQLite keeps,
may contain the engine's statistics tables, constraints, defaults and indexes. The
execution semantics models CREATE TABLE with plain columns only and no CREATE
INDEX, so those are model restrictions for statements that it runs. -/
inductive Mode where
  /-- The statements describe a catalog; nothing runs them. -/
  | description
  /-- The execution semantics runs the statements. -/
  | execution
  deriving Repr, DecidableEq

/-- The inputs of resolution besides the catalog. -/
structure ResolveContext where
  /-- The execution profile, which supplies the limits. -/
  profile : Profile
  /-- Whether the statements describe a catalog or are run. -/
  mode : Mode

/-- The resolution of one statement: the resolved statement and the catalog after
it succeeds, or a model restriction. -/
abbrev StatementResolution := Except Restriction (Resolved.Statement × Catalog)

/-- SQLite's constant-default preparation check for the forms classified here:
literals, time keywords, signs, equality and qualified column references.
Unquoted TRUE and FALSE are constant keywords; other nested identifiers are
column references. SQLite refuses qualified column references as nonconstant
defaults. This is a SQLite rule. For example,
{lean}`constantDefaultExpression (.compare .eq (.numeric "1") (.numeric "1"))` is true.
For the other expression forms, return true to leave their existing model
restriction in control; true does not establish that SQLite accepts those forms.
These checks describe SQLite preparation errors. Supported-domain admission and
default evaluation are separate. -/
def constantDefaultExpression : Syntax.Expr → Bool
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ => true
  | .identifier name quote => quote == .none && booleanKeywordName name
  | .negate operand | .positive operand | .collate operand _ => constantDefaultExpression operand
  | .qualified .. => false
  | .compare .eq left right => constantDefaultExpression left && constantDefaultExpression right
  | .compare .ne .. | .compare .lt .. | .compare .le .. | .compare .gt .. | .compare .ge ..
  | .compare .is .. | .compare .isNot .. => true
  | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. => true
  | .arithmetic .. | .cast .. => true

/-- SQLite's constant-default preparation check for a written DEFAULT, with the
classification scope of {name}`constantDefaultExpression`. A bare identifier is permitted:
TRUE and FALSE are boolean keywords, and other names are stored as text. Other
expressions use {name}`constantDefaultExpression`, including its permissive
classification of forms that remain model restrictions. For example,
{lean}`constantDefault (.identifier (name! "hello") .none)` is true. Omit the DEFAULT
constraint when a column needs no default. -/
def constantDefault (expression : Syntax.Expr) : Bool :=
  match expression with
  | .identifier .. => true
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call ..
  | .arithmetic .. | .cast .. | .qualified .. | .collate .. => constantDefaultExpression expression

/-- Whether the constraint is PRIMARY KEY. -/
def Syntax.ColumnConstraint.isPrimaryKey : Syntax.ColumnConstraint → Bool
  | .primaryKey .. => true
  | .notNull _ | .unique _ | .default _ _ | .collate _ => false

/-- The name of a {lit}`COLLATE` constraint that names no collation ({name}`Collation.named?`),
which SQLite refuses with {lit}`no such collation sequence`; none for every other constraint. -/
def Syntax.ColumnConstraint.unknownCollation : Syntax.ColumnConstraint → Option Identifier
  | .collate name => if (Collation.named? name).isSome then none else some name
  | .notNull _ | .primaryKey .. | .unique _ | .default _ _ => none

/-- Whether the constraint is UNIQUE. -/
def Syntax.ColumnConstraint.isUnique : Syntax.ColumnConstraint → Bool
  | .unique _ => true
  | .notNull _ | .primaryKey .. | .default _ _ | .collate _ => false

/-- Whether the constraint is a DEFAULT that SQLite refuses as not constant. -/
def Syntax.ColumnConstraint.nonconstantDefault : Syntax.ColumnConstraint → Bool
  | .default value _ => !constantDefault value
  | .notNull _ | .primaryKey .. | .unique _ | .collate _ => false

/-- Whether the model describes a catalog default: a literal whose value or
SQLite preparation error is modeled, or a time keyword such as {lit}`CURRENT_TIMESTAMP`, which is kept
without evaluating it. Compound expressions remain model restrictions. Constraints
without a default pass this check. -/
def Syntax.ColumnConstraint.modeledDefault : Syntax.ColumnConstraint → Bool
  | .default (.currentTime _) _ => true
  | .default expression _ => match literalDefault expression with
    | .ok _ | .error (.prepare _) => true
    | .error (.restriction ..) => false
  | .notNull _ | .primaryKey .. | .unique _ | .collate _ => true

/-- A prepare error leaves the catalog unchanged. -/
def prepareError (catalog : Catalog) (error : PrepareError) : StatementResolution :=
  .ok (.prepareError error, catalog)

/-- A model restriction at a path of statement {lit}`index`. -/
def restrict (index : Nat) (path : List Nat) (kind : RestrictionKind) : StatementResolution :=
  .error { statement := index, path := path, kind := kind }

/-- Turn a value issue into the statement's resolution: a prepare error keeps the
catalog, a restriction refuses the script. -/
def issueResolution (catalog : Catalog) (index : Nat) (path : List Nat) : ValueIssue → StatementResolution
  | .prepare error => prepareError catalog (.expression error)
  | .restriction inner reason => restrict index (path ++ inner) reason

end Belay.Sqlite
