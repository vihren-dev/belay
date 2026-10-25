import Belay

open Belay.Sqlite Lean Elab Meta

namespace ReplayFixture

/-! Replay must describe the checked values, preserve original SQL/bindings, and refuse
forged metadata or compiled implementations that differ from the kernel's definitions. -/

/-- Quoted identifiers, quotes, NULL, BLOBs, NUL text and non-ASCII case all survive replay. -/
def sample : Database := db! r#"CREATE TABLE "t""q"(x TEXT COLLATE NOCASE, b BLOB, n);
INSERT INTO "t""q" VALUES('a''b', X'00FF', NULL),('æ',X'',1),('Æ',X'27',2),
(CAST(X'610062' AS TEXT), X'FF00', 3)"#

/-- Original parameterized SQL, rather than SQL with substituted result literals. -/
def replayQuery (wanted : Value) : Script := sql r#"SELECT hex(x), hex(b), n, x = $wanted
FROM "t""q" ORDER BY n"#

/-- Parameter slots preserve both storage classes and all bytes. -/
def parameters : Script := (sql "SELECT typeof(:blob),hex(:blob),typeof(:text),hex(:text),:null IS NULL")
  (.blob [0,255,39]) (.text [97,0,39,255]) .null

/-- These are the two positive integers whose SUM exceeds the signed SQLite range. -/
def overflow : Database := db! "CREATE TABLE t(x); INSERT INTO t VALUES(4611686018427387904),(4611686018427387904)"

def sumQuery : Script := sql "SELECT SUM(x) FROM t"
def clockQuery : Script := sql "SELECT CURRENT_TIMESTAMP"
def unknownQuery : Script := sql "SELECT random()"
def counterQuery : Script := sql "SELECT changes()"
def oneQuery : Script := sql "SELECT 1"
def twoQuery : Script := sql "SELECT 2"
def missingShellTable : Script := sql "SELECT count(*) FROM sqlite_parameters"
def boundShellTable : Script := (sql "SELECT :n FROM sqlite_parameters") (.integer 1)
def shellMetadata : Script := (sql "SELECT name FROM pragma_table_info('sqlite_parameters') WHERE cid=:i")
  (.integer 0)
def numericParameters : Script := (sql "SELECT ?, ?3, ?1; SELECT ?2") (.integer 8) (.integer 9) (.integer 10)
def numericBoundaries : Script := (sql "SELECT :lo,:hi,typeof(:r),:r=1.5")
  (.integer (-9223372036854775808)) (.integer 9223372036854775807) (.real (1.5 : Float).toBits)
def dropShellTable : Script := (sql "DROP TABLE IF EXISTS sqlite_parameters; SELECT :x") (.integer 17)

#guard Replay.valueLiteral (.real (1.5 : Float).toBits) == some "1.5"
#guard (Replay.valueLiteral (.real 0x8000000000000000)).isNone
#guard (Replay.valueLiteral (.integer 9223372036854775808)).isNone

/-- An untrusted compiled implementation supplies a different script from its definition. -/
@[implemented_by twoQuery] def dishonestScript : Script := oneQuery

/-- The same attack against database evaluation must fail its raw-value equality check. -/
@[implemented_by sample] def dishonestDatabase : Database := Database.empty

end ReplayFixture
