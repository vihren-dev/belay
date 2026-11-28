-- Native SQLite probes for the semantic decisions of query results as bags.
-- Each probe runs the same query under two plans, or shows the plan with EXPLAIN QUERY PLAN.
-- One statement per line: the shell skips the rest of a line after an error.
.print == SQLite version
SELECT sqlite_version();
CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, p INTEGER);
INSERT INTO customers VALUES (1, 'bob', 1), (2, 'ada', 1);
.print == P0 the queries of CurrentOutputs.lean on the guide's customers
SELECT name FROM customers;
SELECT name FROM customers ORDER BY p;
SELECT name FROM customers ORDER BY name;
CREATE TABLE t(id INTEGER PRIMARY KEY, name TEXT, p INTEGER);
INSERT INTO t VALUES (1, 'bob', 1), (2, 'ada', 1), (3, 'cy', 2);
.print == P1 LIMIT 1 without ORDER BY: rowid scan, then an index on name
SELECT name FROM t NOT INDEXED LIMIT 1;
CREATE INDEX t_name ON t(name);
SELECT name FROM t INDEXED BY t_name LIMIT 1;
.print == P2 rows without ORDER BY and with ORDER BY name
SELECT name FROM t NOT INDEXED;
SELECT name FROM t ORDER BY name;
.print == P3 a tie of ORDER BY p: rowid scan, then an index on (p, name)
SELECT name FROM t NOT INDEXED ORDER BY p;
CREATE INDEX t_p_name ON t(p, name);
SELECT name FROM t INDEXED BY t_p_name ORDER BY p;
CREATE TABLE u(id INTEGER PRIMARY KEY, name TEXT);
INSERT INTO u VALUES (1, 'a'), (2, 'A'), (3, 'b');
.print == P4 the row that DISTINCT keeps under NOCASE: rowid scan, then a BINARY index
SELECT DISTINCT name COLLATE NOCASE FROM u NOT INDEXED;
CREATE INDEX u_name ON u(name);
SELECT DISTINCT name COLLATE NOCASE FROM u INDEXED BY u_name;
.print == P5 the row that GROUP BY shows under NOCASE: rowid scan, then a BINARY index
SELECT name, count(*) FROM u NOT INDEXED GROUP BY name COLLATE NOCASE;
SELECT name, count(*) FROM u INDEXED BY u_name GROUP BY name COLLATE NOCASE;
.print == P6 group_concat: rowid scan, index scan, and ORDER BY in the aggregate
SELECT group_concat(name, ',') FROM t NOT INDEXED;
SELECT group_concat(name, ',') FROM t INDEXED BY t_name;
SELECT group_concat(name, ',' ORDER BY name DESC) FROM t;
CREATE TABLE r(id INTEGER PRIMARY KEY, x REAL);
INSERT INTO r VALUES (1, 1e308), (2, 1e308), (3, -1e308);
.print == P7 sum, total and avg of REAL values: rowid scan, then an index on x
SELECT sum(x), total(x), avg(x) FROM r NOT INDEXED;
CREATE INDEX r_x ON r(x);
SELECT sum(x), total(x), avg(x) FROM r INDEXED BY r_x;
CREATE TABLE s(id INTEGER PRIMARY KEY, x REAL);
INSERT INTO s VALUES (1, 1e16), (2, 1.0), (3, -1e16), (4, 1.0);
.print == P8 sum of REAL values without overflow: rowid scan, then an index on x
SELECT sum(x) FROM s NOT INDEXED;
CREATE INDEX s_x ON s(x);
SELECT sum(x) FROM s INDEXED BY s_x;
.print == P9 a CTE with LIMIT that the query reads two times: default, MATERIALIZED, NOT MATERIALIZED
WITH k AS (SELECT name FROM t LIMIT 1) SELECT a.name, b.name FROM k AS a, k AS b;
EXPLAIN QUERY PLAN WITH k AS (SELECT name FROM t LIMIT 1) SELECT a.name, b.name FROM k AS a, k AS b;
EXPLAIN QUERY PLAN WITH k AS MATERIALIZED (SELECT name FROM t LIMIT 1) SELECT a.name, b.name FROM k AS a, k AS b;
EXPLAIN QUERY PLAN WITH k AS NOT MATERIALIZED (SELECT name FROM t LIMIT 1) SELECT a.name, b.name FROM k AS a, k AS b;
.print == P10 a scalar subquery with LIMIT: uncorrelated, then correlated
SELECT o.id, (SELECT name FROM t LIMIT 1) FROM t AS o ORDER BY o.id;
EXPLAIN QUERY PLAN SELECT o.id, (SELECT name FROM t LIMIT 1) FROM t AS o ORDER BY o.id;
SELECT o.id, (SELECT name FROM t WHERE t.id <> o.id LIMIT 1) FROM t AS o ORDER BY o.id;
EXPLAIN QUERY PLAN SELECT o.id, (SELECT name FROM t WHERE t.id <> o.id LIMIT 1) FROM t AS o ORDER BY o.id;
.print == P11 a scalar subquery reads the first row of its ORDER BY
SELECT (SELECT name FROM t ORDER BY name);
SELECT (SELECT name FROM t ORDER BY name DESC);
.print == P12 ORDER BY in a FROM subquery: the outer query keeps the order
SELECT group_concat(name, ',') FROM (SELECT name FROM t ORDER BY name);
SELECT group_concat(name, ',') FROM (SELECT name FROM t ORDER BY name DESC);
SELECT name FROM (SELECT name FROM t ORDER BY name DESC);
EXPLAIN QUERY PLAN SELECT name FROM (SELECT name FROM t ORDER BY name DESC);
.print == P13 ORDER BY in a FROM subquery that is part of a join
CREATE TABLE w(k INTEGER);
INSERT INTO w VALUES (1);
SELECT a.name FROM (SELECT name FROM t ORDER BY name DESC) AS a, w;
EXPLAIN QUERY PLAN SELECT a.name FROM (SELECT name FROM t ORDER BY name DESC) AS a, w;
.print == P14 ORDER BY in an IN subquery and an EXISTS subquery
SELECT name FROM t NOT INDEXED WHERE name IN (SELECT name FROM t ORDER BY name DESC);
SELECT count(*) FROM t WHERE EXISTS (SELECT 1 FROM t ORDER BY name DESC);
CREATE TABLE e(x);
INSERT INTO e VALUES (1), (2);
.print == P15 a sort key that fails in an IN subquery: a column without an index, then the rowid
SELECT 1 IN (SELECT x FROM e);
SELECT 1 IN (SELECT x FROM e ORDER BY abs(-9223372036854775808));
SELECT 1 IN (SELECT id FROM t ORDER BY abs(-9223372036854775808));
CREATE TABLE i(id INTEGER PRIMARY KEY, x INTEGER);
INSERT INTO i VALUES (1, 9223372036854775807), (2, 1), (3, -1);
.print == P16 sum of integers that overflows in one order: rowid scan, then an index on x
SELECT sum(x) FROM i NOT INDEXED;
CREATE INDEX i_x ON i(x);
SELECT sum(x) FROM i INDEXED BY i_x;
