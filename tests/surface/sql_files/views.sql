-- +goose Up
CREATE VIEW active AS SELECT email FROM users WHERE name IS NOT NULL;
-- +goose Down
DROP VIEW active;
