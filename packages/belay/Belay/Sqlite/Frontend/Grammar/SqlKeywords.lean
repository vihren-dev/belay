set_option doc.verso true

/-! The words that a correction never writes without quotes (the editor task, part 2b). -/

namespace Belay.Sqlite

/-- The keywords of SQLite 3.51 in lowercase. A name that is one of them, or that SQLite reads
as a literal ({lit}`current_date`), is written in double quotes by a correction, because a bare
keyword changes the statement or makes the parser refuse it. The list is larger than needed:
SQLite reads some of these words as names in some places, and a quoted name is always valid. -/
def sqliteKeywords : List String :=
  ["abort", "action", "add", "after", "all", "alter", "always", "analyze", "and", "as", "asc", "attach",
    "autoincrement", "before", "begin", "between", "by", "cascade", "case", "cast", "check", "collate",
    "column", "commit", "conflict", "constraint", "create", "cross", "current", "current_date",
    "current_time", "current_timestamp", "database", "default", "deferrable", "deferred", "delete",
    "desc", "detach", "distinct", "do", "drop", "each", "else", "end", "escape", "except", "exclude",
    "exclusive", "exists", "explain", "fail", "false", "filter", "first", "following", "for", "foreign",
    "from", "full", "generated", "glob", "group", "groups", "having", "if", "ignore", "immediate", "in",
    "index", "indexed", "initially", "inner", "insert", "instead", "intersect", "into", "is", "isnull",
    "join", "key", "last", "left", "like", "limit", "match", "materialized", "natural", "no", "not",
    "nothing", "notnull", "null", "nulls", "of", "offset", "on", "or", "order", "others", "outer", "over",
    "partition", "plan", "pragma", "preceding", "primary", "query", "raise", "range", "recursive",
    "references", "regexp", "reindex", "release", "rename", "replace", "restrict", "returning", "right",
    "rollback", "row", "rows", "savepoint", "select", "set", "table", "temp", "temporary", "then", "ties",
    "to", "transaction", "trigger", "true", "unbounded", "union", "unique", "update", "using", "vacuum",
    "values", "view", "virtual", "when", "where", "window", "with", "without"]

end Belay.Sqlite
