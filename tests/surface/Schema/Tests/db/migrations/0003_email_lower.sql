ALTER TABLE customers ADD COLUMN email_lower TEXT;
UPDATE customers SET email_lower = lower(email);
