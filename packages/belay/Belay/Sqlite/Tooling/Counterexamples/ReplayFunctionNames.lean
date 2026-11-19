import Belay.Sqlite.Tooling.Counterexamples.ReplaySyntaxExpr

set_option doc.verso true

/-! Recover operator and function spellings for resolved catalog expressions.
Replay validates the reconstructed database before it reports a counterexample. -/

namespace Belay.Sqlite.Replay
open Belay.Sqlite.Model

/-- The SQL spelling of a resolved JSON function. The two arrow functions are infix operators. -/
def jsonFunctionSql : Resolved.JsonFunction → String
  | .extract => "json_extract"
  | .arrowJson => "->"
  | .arrowValue => "->>"
  | .typeName => "json_type"
  | .valid => "json_valid"
  | .arrayLength => "json_array_length"
  | .json => "json"
  | .quote => "json_quote"
  | .array => "json_array"
  | .object => "json_object"
  | .set => "json_set"
  | .insert => "json_insert"
  | .replace => "json_replace"
  | .remove => "json_remove"
  | .patch => "json_patch"
  | .pretty => "json_pretty"
  | .errorPosition => "json_error_position"
  | .jsonb => "jsonb"
  | .jsonbExtract => "jsonb_extract"
  | .jsonbArray => "jsonb_array"
  | .jsonbObject => "jsonb_object"
  | .jsonbSet => "jsonb_set"
  | .jsonbInsert => "jsonb_insert"
  | .jsonbReplace => "jsonb_replace"
  | .jsonbRemove => "jsonb_remove"
  | .jsonbPatch => "jsonb_patch"

/-- The SQL spelling of a resolved scalar function and the collation required on its first argument. -/
def scalarFunctionSql : Resolved.ScalarFunction → String × Option Collation
  | .typeof => ("typeof", none)
  | .length => ("length", none)
  | .octetLength => ("octet_length", none)
  | .abs => ("abs", none)
  | .sign => ("sign", none)
  | .zeroblob => ("zeroblob", none)
  | .iif => ("iif", none)
  | .nullif coll => ("nullif", some coll)
  | .min coll => ("min", some coll)
  | .max coll => ("max", some coll)
  | .like => ("like", none)
  | .glob => ("glob", none)
  | .lower => ("lower", none)
  | .upper => ("upper", none)
  | .substr => ("substr", none)
  | .instr => ("instr", none)
  | .replace => ("replace", none)
  | .trim .leading => ("ltrim", none)
  | .trim .trailing => ("rtrim", none)
  | .trim .both => ("trim", none)
  | .hex => ("hex", none)
  | .unhex => ("unhex", none)
  | .quote => ("quote", none)
  | .unistrQuote => ("unistr_quote", none)
  | .char => ("char", none)
  | .unicode => ("unicode", none)
  | .unistr => ("unistr", none)
  | .pipes => ("||", none)
  | .concat => ("concat", none)
  | .concatWs => ("concat_ws", none)
  | .round => ("round", none)
  | .floor => ("floor", none)
  | .ceil => ("ceil", none)
  | .trunc => ("trunc", none)
  | .sqrt => ("sqrt", none)
  | .pi => ("pi", none)
  | .degrees => ("degrees", none)
  | .radians => ("radians", none)
  | .mod => ("mod", none)
  | .printf => ("printf", none)

end Belay.Sqlite.Replay
