import Plausible.Sampleable
import Belay.Sqlite.SampleDatabases

set_option doc.verso true

namespace Belay.Sqlite.Sampling

/-- Suggest deleting one row or shrinking one cell, preserving the catalog and the other
rows. Each suggestion is checked for database validity. This only proposes smaller data;
the certificate boundary must still certify any retained counterexample. -/
def shrinkDatabase (database : Database) : List Database :=
  database.raw.rows.zipIdx.flatMap fun (rows, tablePosition) =>
    let deleted := (List.range rows.length).map fun rowPosition =>
      database.raw.setRows tablePosition (rows.eraseIdx rowPosition)
    let cells := rows.zipIdx.flatMap fun (row, rowPosition) =>
      row.values.zipIdx.flatMap fun (value, columnPosition) =>
        (shrinkValue value).map fun smaller =>
          database.raw.setRows tablePosition
            (rows.set rowPosition { row with values := row.values.set columnPosition smaller })
    (deleted ++ cells).filterMap validated

end Belay.Sqlite.Sampling

namespace Belay.Sqlite

/-- Show the raw catalog and rows in Plausible diagnostics; the validity proof is omitted.
For executable SQL replay, use the checker's replay artifact instead of this debug view. -/
instance : Repr Database where
  reprPrec database precedence := reprPrec database.raw precedence

/-- Plausible generates valid databases with the default nullable table {lit}`t(a)` and
at most two rows. For other schemas, use {name}`Sampling.database` with an explicit base.
The SQL checker uses that same generator with the claim's inferred schema and constants. -/
instance : Plausible.Arbitrary Database := ⟨Sampling.database Sampling.defaultSchema⟩

/-- Plausible proposes the checker's validity-preserving row and cell shrinks. The SQL
checker additionally bounds the attempts and recertifies a retained counterexample. -/
instance : Plausible.Shrinkable Database := ⟨Sampling.shrinkDatabase⟩

end Belay.Sqlite
