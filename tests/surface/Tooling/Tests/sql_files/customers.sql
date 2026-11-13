CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
CREATE INDEX customers_by_email ON customers(email);
