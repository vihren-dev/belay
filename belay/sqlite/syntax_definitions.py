"""Map CREATE TABLE, CREATE INDEX and ALTER TABLE ADD COLUMN to statement syntax.

Each production maps to one constructor without reading the schema. Optional
syntax that has no constructor, such as TEMP, IF NOT EXISTS or a schema name, is
refused with its source range.
"""

from .located import Located, constructor, leaf, sequence, structure
from .sql_tree import Node, Tree
from .syntax_constraints import check, constraint_name, declared_type, foreign_key, generated, references
from .syntax_expressions import dequote, expression, identifier, name, term
from .syntax_shapes import MODELED_FORMS, absent, left_list, require

def sort_names(tree: Tree, node: Node) -> Located:
    """Map a key column list of plain names, without sort order, collation or expressions."""
    names: list[Located] = []
    for item in left_list(tree, node, {3: ["expr", "sortorder", "nulls"],
                                       5: ["sortlist", "COMMA", "expr", "sortorder", "nulls"]}):
        expression_node, order, nulls = item[-3:]
        absent(tree, order, "A sort order in a key")
        absent(tree, nulls, "NULLS FIRST or NULLS LAST")
        names.append(name(tree, require(tree, expression_node, ["ID"])[0]))
    return sequence(names, node.start, node.end)


ALGORITHMS = {"ROLLBACK": "rollback", "ABORT": "abort", "FAIL": "fail", "IGNORE": "ignore", "REPLACE": "replace"}
"""SQLite's conflict algorithm keywords and the Lean constructors of `ConflictAlgorithm`."""


def resolve_type(tree: Tree, node: Node) -> Located:
    """Map a `resolvetype` node, `raisetype`, `IGNORE` or `REPLACE`, to its algorithm."""
    (part,) = tree.children(node)
    if part.symbol == "raisetype":
        (part,) = tree.children(part)
    return leaf(ALGORITHMS[part.symbol], node.start, node.end)


def constraint_algorithm(tree: Tree, node: Node) -> Located:
    """Map an `onconf` node: the algorithm of `ON CONFLICT algorithm`, or none."""
    if not node.children:
        return leaf(None, node.start, node.end)
    _, _, kind = require(tree, node, ["ON", "CONFLICT", "resolvetype"])
    return resolve_type(tree, kind)


def column_constraint(tree: Tree, node: Node, current: str | None) -> Located:
    """Map NOT NULL, PRIMARY KEY with its sort order, UNIQUE, each with its ON CONFLICT
    algorithm, COLLATE with its name as written, CHECK with the label of the constraint name
    in effect (`current`), REFERENCES, AS for a generated column, and the DEFAULT forms."""
    children = tree.children(node)
    symbols = [child.symbol for child in children]
    if symbols == ["CHECK", "LP", "expr", "RP"]:
        return check(tree, node, children, current)
    if symbols == ["REFERENCES", "nm", "eidlist_opt", "refargs"]:
        return references(tree, node, children)
    if symbols == ["AS", "generated"]:
        return generated(tree, node, children[1])
    if symbols == ["NOT", "NULL", "onconf"]:
        return constructor("notNull", [("algorithm", constraint_algorithm(tree, children[2]))], node.start, node.end)
    if symbols == ["PRIMARY", "KEY", "sortorder", "onconf", "autoinc"]:
        absent(tree, children[4], "AUTOINCREMENT")
        order = [child.symbol for child in tree.children(children[2])]
        return constructor("primaryKey", [("descending", leaf(order == ["DESC"], children[2].start, children[2].end)),
                                          ("algorithm", constraint_algorithm(tree, children[3]))],
                           node.start, node.end)
    if symbols == ["UNIQUE", "onconf"]:
        return constructor("unique", [("algorithm", constraint_algorithm(tree, children[1]))], node.start, node.end)
    if symbols in (["COLLATE", "ID"], ["COLLATE", "STRING"]):
        return constructor("collate", [("name", name(tree, children[1]))], node.start, node.end)
    if symbols == ["DEFAULT", "scantok", "term"]:
        value = term(tree, children[2])
    elif symbols in (["DEFAULT", "MINUS", "scantok", "term"], ["DEFAULT", "PLUS", "scantok", "term"]):
        kind = "negate" if symbols[1] == "MINUS" else "positive"
        value = constructor(kind, [("operand", term(tree, children[3]))], children[1].start, children[3].end)
    elif symbols == ["DEFAULT", "scantok", "ID"]:
        value = identifier(tree, children[2])
    else:
        raise tree.unsupported(node, "Unsupported column constraint; use NOT NULL, PRIMARY KEY, UNIQUE, "
                               "COLLATE, CHECK, REFERENCES or DEFAULT with a literal")
    source_text = tree.sql[value.start:value.end].decode("utf-8")
    return constructor("default", [("value", value),
                                   ("sourceText", leaf(source_text, value.start, value.end))], node.start, node.end)


def column_definition(tree: Tree, column: Node, constraints: Node) -> tuple[Located, str | None]:
    """Map a column name, its declared type text as SQLite keeps it, and its constraints,
    with the constraint name in effect after them. `CONSTRAINT name` and a deferral clause
    map to no constraint: a name only labels the CHECK constraints after it."""
    column_name, type_token = require(tree, column, ["nm", "typetoken"])
    declared = dequote(declared_type(tree, type_token)) if type_token.children else None
    items: list[Located] = []
    current: str | None = None
    for item in left_list(tree, constraints, {2: ["carglist", "ccons"]}):
        parts = tree.children(item[-1])
        symbols = [part.symbol for part in parts]
        if symbols == ["CONSTRAINT", "nm"]:
            current = constraint_name(tree, parts[1])
        elif symbols != ["defer_subclause"]:
            items.append(column_constraint(tree, item[-1], current))
    return structure([("name", name(tree, column_name)),
                      ("declaredType", leaf(declared, type_token.start, type_token.end)),
                      ("constraints", sequence(items, constraints.start, constraints.end))],
                     column.start, constraints.end), current


def table_constraint(tree: Tree, node: Node, current: str | None) -> Located:
    """Map a table PRIMARY KEY or UNIQUE constraint over plain column names, with its
    ON CONFLICT algorithm, a CHECK with the label of the constraint name in effect
    (`current`), whose ON CONFLICT clause SQLite ignores, and a FOREIGN KEY."""
    children = tree.children(node)
    symbols = [child.symbol for child in children]
    if symbols == ["CHECK", "LP", "expr", "RP", "onconf"]:
        return check(tree, node, children, current)
    if symbols == ["FOREIGN", "KEY", "LP", "eidlist", "RP", "REFERENCES", "nm", "eidlist_opt", "refargs",
                   "defer_subclause_opt"]:
        return foreign_key(tree, node, children)
    if symbols == ["PRIMARY", "KEY", "LP", "sortlist", "autoinc", "RP", "onconf"]:
        absent(tree, children[4], "AUTOINCREMENT")
        return constructor("primaryKey", [("columns", sort_names(tree, children[3])),
                                          ("algorithm", constraint_algorithm(tree, children[6]))], node.start, node.end)
    if symbols == ["UNIQUE", "LP", "sortlist", "RP", "onconf"]:
        return constructor("unique", [("columns", sort_names(tree, children[2])),
                                      ("algorithm", constraint_algorithm(tree, children[4]))], node.start, node.end)
    raise tree.unsupported(node, "Unsupported table constraint; use PRIMARY KEY or UNIQUE over column names, "
                                 "CHECK or FOREIGN KEY")


def table_options(tree: Tree, node: Node) -> Located:
    """Map the table options after the column list: `WITHOUT ROWID` (ADR 0014, slice 2).
    `STRICT` is refused until the model describes it."""
    without_rowid = False
    for item in left_list(tree, node, {1: ["table_option"], 3: ["table_option_set", "COMMA", "table_option"]}):
        option = item[-1]
        if [child.symbol for child in tree.children(option)] == ["WITHOUT", "nm"]:
            without_rowid = True
        else:
            raise tree.unsupported(option, "The table option STRICT is not modeled; remove it")
    return structure([("withoutRowid", leaf(without_rowid, node.start, node.end))], node.start, node.end)


def create_table(tree: Tree, command: Node) -> Located:
    """Map CREATE TABLE with column definitions and table constraints."""
    declaration, arguments = require(tree, command, ["create_table", "create_table_args"])
    header = require(tree, declaration, ["createkw", "temp", "TABLE", "ifnotexists", "nm", "dbnm"])
    body = require(tree, arguments, ["LP", "columnlist", "conslist_opt", "RP", "table_option_set"])
    absent(tree, header[1], "TEMP")
    absent(tree, header[3], "IF NOT EXISTS")
    absent(tree, header[5], "A schema name")
    column_shapes = {2: ["columnname", "carglist"], 4: ["columnlist", "COMMA", "columnname", "carglist"]}
    columns: list[Located] = []
    current: str | None = None
    for item in left_list(tree, body[1], column_shapes):
        definition, current = column_definition(tree, item[-2], item[-1])
        columns.append(definition)
    constraints: list[Located] = []
    if body[2].children:
        _, listed = require(tree, body[2], ["COMMA", "conslist"])
        # The name of the last column stays in effect until a comma between table constraints.
        for item in left_list(tree, listed, {1: ["tcons"], 3: ["conslist", "tconscomma", "tcons"]}):
            if len(item) == 2 and item[0].children:
                current = None
            parts = tree.children(item[-1])
            if [part.symbol for part in parts] == ["CONSTRAINT", "nm"]:
                current = constraint_name(tree, parts[1])
            else:
                constraints.append(table_constraint(tree, item[-1], current))
    return constructor("createTable", [("name", name(tree, header[4])),
                                       ("columns", sequence(columns, body[1].start, body[1].end)),
                                       ("constraints", sequence(constraints, body[2].start, body[2].end)),
                                       ("options", table_options(tree, body[4]))],
                       command.start, command.end)


def add_column(tree: Tree, command: Node) -> Located:
    """Map ALTER TABLE ADD [COLUMN] for an unqualified table name."""
    parts = require(tree, command, ["ALTER", "TABLE", "add_column_fullname", "ADD", "kwcolumn_opt", "columnname",
                                    "carglist"])
    (full,) = require(tree, parts[2], ["fullname"])
    (table,) = require(tree, full, ["nm"])
    return constructor("addColumn", [("table", name(tree, table)),
                                     ("column", column_definition(tree, parts[5], parts[6])[0])],
                       command.start, command.end)
