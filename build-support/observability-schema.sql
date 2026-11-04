-- ADR 0028 contract export. Devops deployment matching is pending (devops#47).
CREATE DATABASE IF NOT EXISTS belay_observability;

CREATE TABLE IF NOT EXISTS belay_observability.test_executions
(
    execution_id UUID,
    started_at DateTime64(6, 'UTC'),
    metadata String DEFAULT '{}'
)
ENGINE = ReplacingMergeTree
ORDER BY execution_id;

CREATE TABLE IF NOT EXISTS belay_observability.test_events
(
    execution_id UUID,
    event_id UUID,
    test_node_id Nullable(String),
    kind String,
    data String
)
ENGINE = ReplacingMergeTree
ORDER BY (execution_id, event_id);

CREATE VIEW IF NOT EXISTS belay_observability.test_executions_unique AS
SELECT * FROM belay_observability.test_executions FINAL;

CREATE VIEW IF NOT EXISTS belay_observability.test_events_unique AS
SELECT * FROM belay_observability.test_events FINAL;
