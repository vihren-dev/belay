import Lean.LabelAttribute
import Belay.Sqlite.Model.Programs.Scripts.PlainDeleteCoverage

set_option doc.verso true

/-! The row facts for DELETE coverage form an extensible set for proof search. -/

/-- Facts that discharge a plain DELETE filter's row-safety check. -/
register_label_attr delete_row_fact

