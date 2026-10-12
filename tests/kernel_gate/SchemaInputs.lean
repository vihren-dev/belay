import SqliteVerifier

/-! The supplied starting catalog is generated independently of every user module. -/
namespace Generated
open Belay.Sqlite
/-- The documented SQLite 3.51.0 profile. -/
def profile : Profile := Profile.documented "3.51.0" "2025-11-04 19:38:17 fb2c931ae597f8d00a37574ff67aeed3eced4e5547f9120744ae4bfa8e74527b"
/-- The schema has no statements. -/
def schema : List Syntax.Statement := []
/-- The starting catalog is empty. -/
def startCatalog : Catalog := []
end Generated
