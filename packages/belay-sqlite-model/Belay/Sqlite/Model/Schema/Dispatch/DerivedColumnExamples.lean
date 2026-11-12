import Belay.Sqlite.Model.Schema.Dispatch.CompoundResolutionExamples
import Belay.Sqlite.Model.Queries.Select.DerivedColumnExamples

set_option doc.verso true

/-! Kernel checks of query-source column metadata and the compound ORDER BY COLLATE
rewrite (ADR 0019, D3 and D5). The examples distinguish every column's affinity, a literal's
absent affinity, compound type conflicts, and explicit versus column collation. -/

namespace Belay.Sqlite.Model.Resolution.DerivedColumnExamples

open Syntax Resolution.Examples Resolution.CollationExamples Resolution.CompoundResolutionExamples

/-- The rewritten IN column obtains numeric affinity from the first term, unlike ordinary
compound IN, which reads the final term's expression affinity. -/
example : rowsOf (inCompound (.string [49]) [.union]
    [term [shown (.cast (num "1") "INTEGER")] none (some 0), term [shown (num "5")] none (some 0)]
    rewrittenOrder) = some [[.integer 1]] := by decide +kernel

/-- A scalar subquery keeps no collation even when its derived output column has NOCASE. -/
example : rowsOf (.select [shown (.compare .eq (.string [65]) (.subquery 0))] none [] none [] [] none none
    [{ compoundSubquery [.union] rewrittenOrder with limit := some (num "1") },
     term [shown (.collate (.string [97]) (name! "NOCASE"))] none (some 0),
     term [shown (.string [98])] none (some 0)]) = some [[.integer 0]] := by decide +kernel

/-- The rewrite turns an explicit NOCASE into a column collation, so the left operand's
BINARY column collation takes precedence in IN. -/
example : let catalog := catalogOf (schema [.createTable (name! "x") [column (name! "a") (some "TEXT")] []])
    let statement := Syntax.Statement.select [shown (.inQuery (ref (name! "a")) 0 false)]
      (some { table := name! "x", alias := none }) [] none [] [] none none
      [compoundSubquery [.union] rewrittenOrder,
       term [shown (.collate (.string [97]) (name! "NOCASE"))] none (some 0),
       term [shown (.string [98])] none (some 0)]
    ((statements (migration catalog [statement])).head?.bind fun
      | .query query _ => query.columns.head?
      | _ => none) = some (.scalar (.inQuery (.column 0) 0 (some .text) .binary false)) := by decide +kernel

end Belay.Sqlite.Model.Resolution.DerivedColumnExamples
