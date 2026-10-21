import Belay.Sqlite.Translation.Statements

set_option doc.verso true

/-! The translation of SQL text to the model's statement syntax with the source range of each
node, a prototype of ADR 0017, S1 (candidate A): {name}`Belay.Sqlite.Translation.translateParse` for a parse tree and
{name}`Belay.Sqlite.Translation.translationJson` for a text and a grammar of the parser library. -/
