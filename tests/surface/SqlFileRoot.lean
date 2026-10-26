import Lean.Elab.Command
import Belay.Sqlite.SqlFileLoad

open Belay.Sqlite Lean Elab Command System

/-! The explicit-root primitive and the option's root resolution, without a Lake workspace. -/

/-- Run an IO action that must fail with a message containing the needle. -/
def expectFailure (label : String) (action : IO α) (needle : String) : CommandElabM Unit := do
  match ← (action.toBaseIO : IO _) with
  | .ok _ => throwError "{label}: unexpectedly succeeded"
  | .error error =>
    unless (toString error).contains needle do
      throwError "{label}: expected {needle}, got {error}"

elab "check_explicit_root" : command => do
  IO.FS.withTempDir fun directory => do
    IO.FS.createDirAll (directory / "sql")
    IO.FS.createDirAll (directory / "lean")
    IO.FS.writeFile (directory / "sql/a.sql") "SELECT 1;\r\n-- é\r\n"
    IO.FS.writeFile (directory / "lean/Q.lean") ""
    IO.FS.writeFile (directory / "plain") ""
    let source ← readSqlFileSourceAtRoot directory "fixture" "sql/a.sql"
    unless source.text == "SELECT 1;\r\n-- é\r\n" && source.path == "sql/a.sql" && source.package == "fixture" do
      throwError "explicit root changed the file text or identity"
    -- The compiled identity has no root: a different checkout reads the same relative record.
    unless source.root == (← IO.FS.realPath directory) do throwError "explicit root was not canonical"
    expectFailure "absolute" (readSqlFileSourceAtRoot directory "fixture" (directory / "sql/a.sql")) "is absolute"
    expectFailure "escape" (readSqlFileSourceAtRoot directory "fixture" "sql/../../a.sql") "leaves the package"
    expectFailure "missing" (readSqlFileSourceAtRoot directory "fixture" "sql/none.sql") "cannot read SQL file sql/none.sql"
    expectFailure "not a directory" (readSqlFileSourceAtRoot (directory / "plain") "fixture" "a.sql") "not a directory"
    expectFailure "missing root" (readSqlFileSourceAtRoot (directory / "nope") "fixture" "a.sql") "not a directory"
    -- The option anchors at the Lean file's directory, not the process directory.
    let up ← sqlOverrideRoot (directory / "lean/Q.lean") ".."
    unless (← IO.FS.realPath up) == (← IO.FS.realPath directory) do throwError "option root was not anchored at the Lean file"
    expectFailure "absolute option" (sqlOverrideRoot (directory / "lean/Q.lean") "/") "is absolute"
    expectFailure "missing option root" (sqlOverrideRoot (directory / "lean/Q.lean") "nope") "not a directory"
    expectFailure "file option root" (sqlOverrideRoot (directory / "lean/Q.lean") "Q.lean") "not a directory"
  logInfo "explicit root checks passed"

check_explicit_root
