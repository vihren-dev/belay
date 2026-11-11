import Belay.Sqlite.Model.Shared.Resolved.PragmaSource

set_option doc.verso true

/-! The rows of a pragma as a source of {lit}`FROM` (ADR 0019, D2). A pragma statement is a
query over such a source, and so are the table-valued forms {lit}`pragma_table_info('t')` and
{lit}`pragma_foreign_key_list('t')`, so that both forms have one meaning. -/

namespace Belay.Sqlite.Model.Resolved

/-- The number of cells of each row of the pragma. -/
def PragmaRows.width : PragmaRows → Nat
  | .fixed width _ => width
  | .check .. => 1
  | .foreignKeyCheck _ => 4

end Belay.Sqlite.Model.Resolved
