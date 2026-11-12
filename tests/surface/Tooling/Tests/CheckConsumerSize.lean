import Belay

open Belay.Sqlite Lean Elab Term Meta

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_check_consumer_size_test.py`: a schema of the size and
kind of a consumer application (more than 8,192 data nodes, CHECK constraints, foreign keys,
triggers that write another table, and an ALTER TABLE in its text). Deleting a message with no
conversation fails, because the delete trigger logs a NULL conversation and the CHECK of
{lit}`message_log` rejects it. The search finds this with the schema of the premise
{name}`Database.HasCatalog` alone; a counterexample written with {lit}`db!` is also reported. -/

namespace ConsumerSizeFixture

/-- The schema text of the fixture. -/
def consumerText : String := "
  CREATE TABLE users (
    id           INTEGER PRIMARY KEY,
    handle       TEXT NOT NULL UNIQUE,
    display_name TEXT,
    email        TEXT NOT NULL CHECK (instr(email, '@') > 1),
    created_at   INTEGER NOT NULL DEFAULT 0,
    status       TEXT NOT NULL DEFAULT 'active' CHECK (status IN ('active', 'suspended', 'deleted')));
  CREATE TABLE conversations (
    id         INTEGER PRIMARY KEY,
    title      TEXT CHECK (title IS NULL OR length(title) <= 200),
    owner_id   INTEGER REFERENCES users(id) ON DELETE SET NULL,
    created_at INTEGER NOT NULL DEFAULT 0,
    archived   INTEGER NOT NULL DEFAULT 0 CHECK (archived IN (0, 1)));
  CREATE TABLE members (
    conversation_id INTEGER NOT NULL REFERENCES conversations(id) ON DELETE CASCADE,
    user_id         INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    role            TEXT NOT NULL DEFAULT 'member' CHECK (role IN ('owner', 'member')),
    joined_at       INTEGER NOT NULL DEFAULT 0,
    PRIMARY KEY (conversation_id, user_id));
  CREATE TABLE messages (
    id              INTEGER PRIMARY KEY,
    conversation_id INTEGER REFERENCES conversations(id) ON DELETE CASCADE,
    author_id       INTEGER REFERENCES users(id) ON DELETE SET NULL,
    body            TEXT NOT NULL DEFAULT '' CHECK (length(body) <= 4000),
    sent_at         INTEGER NOT NULL DEFAULT 0,
    edited_at       INTEGER CHECK (edited_at IS NULL OR edited_at >= sent_at));
  CREATE TABLE attachments (
    id         INTEGER PRIMARY KEY,
    message_id INTEGER NOT NULL REFERENCES messages(id) ON DELETE CASCADE,
    name       TEXT NOT NULL CHECK (length(name) > 0),
    size       INTEGER NOT NULL CHECK (size >= 0),
    mime       TEXT NOT NULL DEFAULT 'application/octet-stream');
  CREATE TABLE message_log (
    id              INTEGER PRIMARY KEY,
    message_id      INTEGER NOT NULL,
    conversation_id INTEGER CHECK (conversation_id IS NOT NULL),
    action          TEXT NOT NULL CHECK (action IN ('edited', 'deleted')),
    at              INTEGER NOT NULL DEFAULT 0);
  CREATE UNIQUE INDEX users_email ON users (email COLLATE NOCASE);
  CREATE INDEX conversations_owner ON conversations (owner_id);
  CREATE INDEX members_user ON members (user_id);
  CREATE INDEX messages_conversation ON messages (conversation_id, sent_at);
  CREATE INDEX messages_author ON messages (author_id);
  CREATE INDEX attachments_message ON attachments (message_id);
  CREATE INDEX message_log_message ON message_log (message_id);
  CREATE INDEX message_log_conversation ON message_log (conversation_id, at);
  CREATE TRIGGER log_message_delete AFTER DELETE ON messages BEGIN
    INSERT INTO message_log (message_id, conversation_id, action) VALUES (old.id, old.conversation_id, 'deleted');
  END;
  CREATE TRIGGER log_message_edit AFTER UPDATE OF body ON messages BEGIN
    INSERT INTO message_log (message_id, conversation_id, action) VALUES (new.id, new.conversation_id, 'edited');
  END;
  CREATE TRIGGER touch_conversation AFTER INSERT ON messages BEGIN
    UPDATE conversations SET archived = 0 WHERE id = new.conversation_id;
  END;
  CREATE TRIGGER remove_member_rows AFTER DELETE ON users BEGIN
    DELETE FROM members WHERE user_id = old.id;
  END;
  CREATE TRIGGER archive_empty AFTER DELETE ON members BEGIN
    UPDATE conversations SET archived = 1
      WHERE id = old.conversation_id AND NOT EXISTS (SELECT 1 FROM members WHERE conversation_id = old.conversation_id);
  END;
  ALTER TABLE messages ADD COLUMN pinned INTEGER NOT NULL DEFAULT 0;"

/-- A {lit}`db!` database of the fixture's schema text followed by the given statements, so the
schema is written once. -/
elab "consumer_db! " extra:str : term => do
  elabTerm (← `(db! $(Syntax.mkStrLit (consumerText ++ extra.getString)))) (some (mkConst ``Database))

/-- The schema of the fixture, without rows. -/
def consumer : Database := consumer_db! ""

/-- The schema with one message that has no conversation: the counterexample written by hand. -/
def orphanMessage : Database := consumer_db! "
  INSERT INTO messages (id, body) VALUES (7, 'hi');"

/-- Delete one message by its id. -/
def deleteMessage (id : Value) : Script := sql r"DELETE FROM messages WHERE id = ?1" id

/-- Mark the message of one command, so the test reads each block. -/
elab "labelled_sql " label:str " in " cmd:command : command => do
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"SQL-COMMAND-END {label.getString}:"

-- The data nodes of the schema as the checker reifies it (`Check.checkDataSize` counts the same
-- nodes), so the test can check that the schema is larger than 8,192 nodes.
#eval show MetaM Unit from do
  let mut pending := #[databaseExpr consumer.raw]
  let mut nodes := 0
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    nodes := nodes + 1
    match current with
    | .app function argument => pending := (pending.push function).push argument
    | .mdata _ body => pending := pending.push body
    | _ => pure ()
  IO.println s!"consumer schema nodes: {nodes}"

set_option maxHeartbeats 4000000

labelled_sql "consumer" in #sql_check ∀ id, Succeeds (deleteMessage id) (·.HasCatalog consumer)

labelled_sql "supplied" in #sql_check ∀ id, Succeeds (deleteMessage id) (·.HasCatalog consumer)
  with (db := orphanMessage) (input id := Value.integer 7)

end ConsumerSizeFixture
