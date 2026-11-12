import Belay.Sqlite.Queries.Automation.SqlSelectRule
import Belay.Sqlite.Tooling.Counterexamples.SelectCatalogCheck

set_option doc.verso true

/-! The built-in rules and evaluation laws of {lit}`sql_select`. Each registration is global, so every
file that imports the tactic has them. The phase rules turn a membership in the results of a query or in
the scanned rows of a table into facts; the evaluation laws ({lit}`sql_select_simp`) are proved equations
that the simplifier uses on these facts and on the goal. An equation that holds only by definition and
that exposes the evaluation of an expression is stated and proved as a theorem, because a definitional
step there makes the kernel unfold the evaluator, which can exceed its recursion depth. -/

namespace Belay.Sqlite.Select

attribute [sql_select_rule execution] Run.query_returnsResult_ofCatalog Sql.check_query_ofCatalog
  Sql.check_query_ofResolveState

end Belay.Sqlite.Select
