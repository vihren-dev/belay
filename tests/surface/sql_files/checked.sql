INSERT INTO users(email, name) VALUES (:email, :name);
SELECT name FROM users WHERE email = :email;
