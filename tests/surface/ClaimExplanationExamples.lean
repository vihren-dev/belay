import Belay

/-! The `#explain` command describes fresh-run claims, ordinary triples and success claims:
entry assumptions, the scope of the captured start, the error policy and the observation context. -/

open Belay.Sqlite Std.Do

#explain ((Sql.pure 1) ensures andOk ⌜True⌝ where sql r"SELECT 1")
#explain ((Sql.pure 1) ensures ifOk (holds (sql r"SELECT 1")))
#explain ((Sql.pure 1) ensures andOk (holdsInContext (sql r"SELECT 1")))
#explain ((Sql.pure 1) ensures (⇓ value => ⌜value = 1⌝))
#explain FreshTriple (Sql.pure 1) (fun _ => True) (fun _ _ _ _ => True)
#explain (⦃fun _ : ExecutionContext => ⌜True⌝⦄ Sql.pure (1 : Nat) ⦃andOk (holds (sql r"SELECT 1"))⦄)
#explain ((Sql.pure 1) succeeds where sql r"SELECT 1")
#explain ((Sql.pure 1) ensures (⇓ value context => ⌜¬ ((andOk ⌜True⌝ : PostCond Nat (.arg ExecutionContext .pure)).1 value context).down⌝))
