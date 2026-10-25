-- name: findByEmail
-- Find a user.
-- Second line.
SELECT * FROM users WHERE email = :email;

-- name: insertUser
INSERT INTO users(email, name) VALUES ($email, ?2);

-- name: trig
CREATE TRIGGER tr AFTER INSERT ON users BEGIN
  -- name: notAMarker
  SELECT '-- name: nope';
  SELECT 1;
END;

/* -- name: blockComment */
-- name: last
SELECT 'x -- name: fake', "-- name: q" FROM users -- name: trailing
