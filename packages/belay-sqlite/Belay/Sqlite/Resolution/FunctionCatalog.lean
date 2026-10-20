import Belay.Sqlite.Declarations

set_option doc.verso true

/-! The built-in functions of the pinned SQLite library (ADR 0015, D1): each name that a call
can name, with the numbers of arguments that its scalar, aggregate or window form accepts,
as {lit}`PRAGMA function_list` of SQLite 3.51.0 gives them: the 141 built-in names, and
{lit}`match`, which the library registers apart and which fails when it runs. Resolution reports
SQLite's {lit}`no such function` and {lit}`wrong number of arguments` from it. A test compares
the table with the native library. -/

namespace Belay.Sqlite

/-- The numbers of arguments that one form of a function accepts: a list of exact numbers,
or every number from a minimum. For example, {lean}`Arity.counts [1, 2]` is the arity of
{lit}`trim`, and {lean}`Arity.atLeast 2` that of {lit}`coalesce`. -/
inductive Arity where
  /-- Exactly one of these numbers of arguments. -/
  | counts (accepted : List Nat)
  /-- Any number of arguments from the minimum on. -/
  | atLeast (minimum : Nat)
  deriving Repr, DecidableEq

/-- Whether the arity accepts the number of arguments. -/
def Arity.accepts : Arity → Nat → Bool
  | .counts accepted, count => accepted.contains count
  | .atLeast minimum, count => minimum ≤ count

/-- A built-in function: the arity of each of its forms, none for a form that it does not
have. {lit}`min` and {lit}`max` have a scalar and an aggregate form; a window function such as
{lit}`rank` has only a window form. -/
structure BuiltinFunction where
  /-- The arity of the scalar function. -/
  scalar : Option Arity := none
  /-- The arity of the aggregate function, which also runs as a window function. -/
  aggregate : Option Arity := none
  /-- The arity of a function that runs only as a window function. -/
  window : Option Arity := none
  deriving Repr, DecidableEq

/-- Whether some form of the function accepts the number of arguments. -/
def BuiltinFunction.accepts (function : BuiltinFunction) (count : Nat) : Bool :=
  [function.scalar, function.aggregate, function.window].any fun arity => arity.any (·.accepts count)

/-- Whether the call is the aggregate form: the aggregate accepts the number of arguments.
SQLite prefers the form whose number of arguments matches exactly, so {lit}`max(x)` is the
aggregate and {lit}`max(x, y)` the scalar function. -/
def BuiltinFunction.isAggregateCall (function : BuiltinFunction) (count : Nat) : Bool :=
  function.aggregate.any (·.accepts count)

/-- The built-in function that a folded name names ({lit}`normalizeIdentifier`), or none for a
name that is no function of the library. -/
def builtinFunction? : String → Option BuiltinFunction
  | "->" => some { scalar := some (.counts [2]) }
  | "->>" => some { scalar := some (.counts [2]) }
  | "abs" => some { scalar := some (.counts [1]) }
  | "acos" => some { scalar := some (.counts [1]) }
  | "acosh" => some { scalar := some (.counts [1]) }
  | "asin" => some { scalar := some (.counts [1]) }
  | "asinh" => some { scalar := some (.counts [1]) }
  | "atan" => some { scalar := some (.counts [1]) }
  | "atan2" => some { scalar := some (.counts [2]) }
  | "atanh" => some { scalar := some (.counts [1]) }
  | "avg" => some { aggregate := some (.counts [1]) }
  | "ceil" => some { scalar := some (.counts [1]) }
  | "ceiling" => some { scalar := some (.counts [1]) }
  | "changes" => some { scalar := some (.counts [0]) }
  | "char" => some { scalar := some (.atLeast 0) }
  | "coalesce" => some { scalar := some (.atLeast 2) }
  | "concat" => some { scalar := some (.atLeast 1) }
  | "concat_ws" => some { scalar := some (.atLeast 2) }
  | "cos" => some { scalar := some (.counts [1]) }
  | "cosh" => some { scalar := some (.counts [1]) }
  | "count" => some { aggregate := some (.counts [0, 1]) }
  | "cume_dist" => some { window := some (.counts [0]) }
  | "current_date" => some { scalar := some (.counts [0]) }
  | "current_time" => some { scalar := some (.counts [0]) }
  | "current_timestamp" => some { scalar := some (.counts [0]) }
  | "date" => some { scalar := some (.atLeast 0) }
  | "datetime" => some { scalar := some (.atLeast 0) }
  | "degrees" => some { scalar := some (.counts [1]) }
  | "dense_rank" => some { window := some (.counts [0]) }
  | "exp" => some { scalar := some (.counts [1]) }
  | "first_value" => some { window := some (.counts [1]) }
  | "floor" => some { scalar := some (.counts [1]) }
  | "format" => some { scalar := some (.atLeast 0) }
  | "glob" => some { scalar := some (.counts [2]) }
  | "group_concat" => some { aggregate := some (.counts [1, 2]) }
  | "hex" => some { scalar := some (.counts [1]) }
  | "if" => some { scalar := some (.atLeast 2) }
  | "ifnull" => some { scalar := some (.counts [2]) }
  | "iif" => some { scalar := some (.atLeast 2) }
  | "instr" => some { scalar := some (.counts [2]) }
  | "json" => some { scalar := some (.counts [1]) }
  | "json_array" => some { scalar := some (.atLeast 0) }
  | "json_array_length" => some { scalar := some (.counts [1, 2]) }
  | "json_error_position" => some { scalar := some (.counts [1]) }
  | "json_extract" => some { scalar := some (.atLeast 0) }
  | "json_group_array" => some { aggregate := some (.counts [1]) }
  | "json_group_object" => some { aggregate := some (.counts [2]) }
  | "json_insert" => some { scalar := some (.atLeast 0) }
  | "json_object" => some { scalar := some (.atLeast 0) }
  | "json_patch" => some { scalar := some (.counts [2]) }
  | "json_pretty" => some { scalar := some (.counts [1, 2]) }
  | "json_quote" => some { scalar := some (.counts [1]) }
  | "json_remove" => some { scalar := some (.atLeast 0) }
  | "json_replace" => some { scalar := some (.atLeast 0) }
  | "json_set" => some { scalar := some (.atLeast 0) }
  | "json_type" => some { scalar := some (.counts [1, 2]) }
  | "json_valid" => some { scalar := some (.counts [1, 2]) }
  | "jsonb" => some { scalar := some (.counts [1]) }
  | "jsonb_array" => some { scalar := some (.atLeast 0) }
  | "jsonb_extract" => some { scalar := some (.atLeast 0) }
  | "jsonb_group_array" => some { aggregate := some (.counts [1]) }
  | "jsonb_group_object" => some { aggregate := some (.counts [2]) }
  | "jsonb_insert" => some { scalar := some (.atLeast 0) }
  | "jsonb_object" => some { scalar := some (.atLeast 0) }
  | "jsonb_patch" => some { scalar := some (.counts [2]) }
  | "jsonb_remove" => some { scalar := some (.atLeast 0) }
  | "jsonb_replace" => some { scalar := some (.atLeast 0) }
  | "jsonb_set" => some { scalar := some (.atLeast 0) }
  | "julianday" => some { scalar := some (.atLeast 0) }
  | "lag" => some { window := some (.counts [1, 2, 3]) }
  | "last_insert_rowid" => some { scalar := some (.counts [0]) }
  | "last_value" => some { window := some (.counts [1]) }
  | "lead" => some { window := some (.counts [1, 2, 3]) }
  | "length" => some { scalar := some (.counts [1]) }
  | "like" => some { scalar := some (.counts [2, 3]) }
  | "likelihood" => some { scalar := some (.counts [2]) }
  | "likely" => some { scalar := some (.counts [1]) }
  | "ln" => some { scalar := some (.counts [1]) }
  | "load_extension" => some { scalar := some (.counts [1, 2]) }
  | "log" => some { scalar := some (.counts [1, 2]) }
  | "log10" => some { scalar := some (.counts [1]) }
  | "log2" => some { scalar := some (.counts [1]) }
  | "lower" => some { scalar := some (.counts [1]) }
  | "ltrim" => some { scalar := some (.counts [1, 2]) }
  | "match" => some { scalar := some (.counts [2]) }
  | "max" => some { scalar := some (.atLeast 1), aggregate := some (.counts [1]) }
  | "median" => some { aggregate := some (.counts [1]) }
  | "min" => some { scalar := some (.atLeast 1), aggregate := some (.counts [1]) }
  | "mod" => some { scalar := some (.counts [2]) }
  | "nth_value" => some { window := some (.counts [2]) }
  | "ntile" => some { window := some (.counts [1]) }
  | "nullif" => some { scalar := some (.counts [2]) }
  | "octet_length" => some { scalar := some (.counts [1]) }
  | "percent_rank" => some { window := some (.counts [0]) }
  | "percentile" => some { aggregate := some (.counts [2]) }
  | "percentile_cont" => some { aggregate := some (.counts [2]) }
  | "percentile_disc" => some { aggregate := some (.counts [2]) }
  | "pi" => some { scalar := some (.counts [0]) }
  | "pow" => some { scalar := some (.counts [2]) }
  | "power" => some { scalar := some (.counts [2]) }
  | "printf" => some { scalar := some (.atLeast 0) }
  | "quote" => some { scalar := some (.counts [1]) }
  | "radians" => some { scalar := some (.counts [1]) }
  | "random" => some { scalar := some (.counts [0]) }
  | "randomblob" => some { scalar := some (.counts [1]) }
  | "rank" => some { window := some (.counts [0]) }
  | "replace" => some { scalar := some (.counts [3]) }
  | "round" => some { scalar := some (.counts [1, 2]) }
  | "row_number" => some { window := some (.counts [0]) }
  | "rtrim" => some { scalar := some (.counts [1, 2]) }
  | "sign" => some { scalar := some (.counts [1]) }
  | "sin" => some { scalar := some (.counts [1]) }
  | "sinh" => some { scalar := some (.counts [1]) }
  | "sqlite_compileoption_get" => some { scalar := some (.counts [1]) }
  | "sqlite_compileoption_used" => some { scalar := some (.counts [1]) }
  | "sqlite_log" => some { scalar := some (.counts [2]) }
  | "sqlite_source_id" => some { scalar := some (.counts [0]) }
  | "sqlite_version" => some { scalar := some (.counts [0]) }
  | "sqrt" => some { scalar := some (.counts [1]) }
  | "strftime" => some { scalar := some (.atLeast 0) }
  | "string_agg" => some { aggregate := some (.counts [2]) }
  | "substr" => some { scalar := some (.counts [2, 3]) }
  | "substring" => some { scalar := some (.counts [2, 3]) }
  | "subtype" => some { scalar := some (.counts [1]) }
  | "sum" => some { aggregate := some (.counts [1]) }
  | "tan" => some { scalar := some (.counts [1]) }
  | "tanh" => some { scalar := some (.counts [1]) }
  | "time" => some { scalar := some (.atLeast 0) }
  | "timediff" => some { scalar := some (.counts [2]) }
  | "total" => some { aggregate := some (.counts [1]) }
  | "total_changes" => some { scalar := some (.counts [0]) }
  | "trim" => some { scalar := some (.counts [1, 2]) }
  | "trunc" => some { scalar := some (.counts [1]) }
  | "typeof" => some { scalar := some (.counts [1]) }
  | "unhex" => some { scalar := some (.counts [1, 2]) }
  | "unicode" => some { scalar := some (.counts [1]) }
  | "unistr" => some { scalar := some (.counts [1]) }
  | "unistr_quote" => some { scalar := some (.counts [1]) }
  | "unixepoch" => some { scalar := some (.atLeast 0) }
  | "unlikely" => some { scalar := some (.counts [1]) }
  | "upper" => some { scalar := some (.counts [1]) }
  | "zeroblob" => some { scalar := some (.counts [1]) }
  | _ => none

end Belay.Sqlite
