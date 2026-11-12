-- The schema of the page for agents (docs/guide/agents.md), before the migration 0003.
CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
CREATE TABLE sessions (id INTEGER PRIMARY KEY,
  customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
  expires_at INTEGER NOT NULL);
