/* The mapping functions of candidate B, one group for each module of belay/sqlite/syntax*.py. */
#ifndef BELAY_SYNTAX_H
#define BELAY_SYNTAX_H
#include "translate.h"

/* names.c: syntax_expressions.py */
char *dequote(T *t, const char *value);
PNode *token(T *t, PNode *node);
Located *name(T *t, PNode *node);
Located *one(T *t, const char *kind, const char *name, Located *value, int start, int end);
Located *term(T *t, PNode *node);
Located *identifier(T *t, PNode *node);
int identifier_token(const char *symbol);
Located *expression(T *t, PNode *node);

/* queries.c and forms.c: syntax_queries.py, syntax_forms.py */
Located *query_expression(T *t, PNode *node);
Located *result_columns(T *t, PNode *node);
Item expression_list(T *t, PNode *node);
Located *alias(T *t, PNode *node);
Located *subquery_form(T *t, PNode *node);
Located *list_form(T *t, PNode *node);

/* select.c and sources.c: syntax_select.py, syntax_sources.py, syntax_subqueries.py */
Fields query_clauses(T *t, PNode *select);
Vec order_terms(T *t, PNode *node);
void from_clause(T *t, PNode *tables, Located **first, Located **joins);
int lift(T *t, PNode *select);
Fields head(Fields fields, int count);
Fields tail(Fields fields, int count);
Located *with_subqueries(T *t, const char *kind, Fields fields, Vec items, int start, int end, Fields after);

/* constraints.c, columns.c and tables.c: syntax_constraints.py, syntax_definitions.py */
int ascii_equal(const char *value, const char *word);
Located *resolve_type(T *t, PNode *node);
Located *constraint_algorithm(T *t, PNode *node);
Located *check(T *t, PNode *node, const char *current);
Located *references(T *t, PNode *node);
Located *generated(T *t, PNode *node, PNode *kind);
Located *deferral(T *t, PNode *node);
Located *foreign_key(T *t, PNode *node);
char *constraint_name(T *t, PNode *node);
char *declared_type(T *t, const char *value);
Located *column_definition(T *t, PNode *column, PNode *constraints, const char **current);
Located *create_table(T *t, PNode *command);
Located *add_column(T *t, PNode *command);

/* conflicts.c and writes.c: syntax_conflicts.py, syntax_writes.py */
Located *assignment_list(T *t, PNode *assignments);
Located *conflict_clauses(T *t, PNode *upsert, PNode **returning);
Located *insert_algorithm(T *t, PNode *operation);
Located *value_rows(T *t, PNode *node);
Located *column_list(T *t, PNode *columns);
Located *transaction(T *t, PNode *command);
Located *insert(T *t, PNode *command);
Located *update(T *t, PNode *command);
Located *delete(T *t, PNode *command);

/* triggers.c and schema.c: syntax_triggers.py, syntax_drops.py, syntax_indexes.py, syntax_pragmas.py */
Located *create_trigger(T *t, PNode *command);
Located *drop(T *t, PNode *command);
Located *create_index(T *t, PNode *command);
Located *pragma(T *t, PNode *command);
#endif
