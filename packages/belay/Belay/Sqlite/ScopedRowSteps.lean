import Belay.Sqlite.ExecutionDeterministic

set_option doc.verso true

/-! Scoped agreement of two single-statement queries (ADR 0017, S8). A call whose script is one query
that gives rows has one branch, its actual run. Two such calls agree under a context relation when
their steps give the same rows and keep their connections, their results are equal on those rows, and
the relation holds for the contexts that the two runs reach. A caller that proves the facts about the
two steps gets the whole scoped agreement of the calls, in both directions and for every branch. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every relation and every pair of contexts, two programs that each send one statement and give
a function of the output: if the first statement continues with the rows {lit}`rows` and keeps the
connection of its context, and the second statement continues with the same rows and keeps the
connection of its context, and the two functions give equal results on those rows, and the relation
holds for the two contexts that the runs reach, then the two programs agree under the relation
({name}`Sql.ScopedAt`). Plain words: two queries that read the same rows and change nothing agree, and
the only remaining duty is the relation for the reached contexts. Proof sketch: an output of rows is not
a choice between results, so each program has one branch ({name}`Sql.ScopedAt.of_one_branch`), and the
two actual runs agree by the premises. -/
theorem Sql.ScopedAt.of_row_steps {β : Type} {related : ExecutionContext → ExecutionContext → Prop}
    {firstStatement secondStatement : Syntax.Statement} {firstValues secondValues : List Value}
    {left right : List Output → β} {first second : ExecutionContext} {rows : List (List Value)}
    (leftStep : runScriptStep runContext first.clock first.index first.connection firstStatement firstValues =
      .continued (.rows rows) first.connection [])
    (rightStep : runScriptStep runContext second.clock second.index second.connection secondStatement
      secondValues = .continued (.rows rows) second.connection [])
    (sameResult : left [.rows rows] = right [.rows rows])
    (closed : related
      (first.finish { outputs := [.rows rows], connection := first.connection, value := some (left [.rows rows]) })
      (second.finish
        { outputs := [.rows rows], connection := second.connection, value := some (right [.rows rows]) })) :
    Sql.ScopedAt related (Sql.exec firstStatement firstValues fun output => .pure (left [output]))
      (Sql.exec secondStatement secondValues fun output => .pure (right [output])) first second := by
  refine Sql.ScopedAt.of_one_branch (by simp [Sql.hasOneBranch, leftStep, Model.Output.choosesResults])
    (by simp [Sql.hasOneBranch, rightStep, Model.Output.choosesResults]) ?_
  simp only [Sql.runFrom, leftStep, rightStep]
  exact ⟨by simp [sameResult], rfl, closed⟩

end Belay.Sqlite
