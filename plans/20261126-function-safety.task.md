# Function safety in expression proofs

Created 2026-11-26. Status DONE.

An expression proof can establish that a modeled scalar, JSON or JSONB call returns a SQL
value from facts about its inputs. Total scalar functions share the existing totality law.
Partial calls expose the conditions on data, paths, flags or limits that their evaluator
checks. JSON subtype flags participate where the function reads them. Date and conditional
expressions keep their existing evaluation laws. The generic call law also applies to
implementations outside the built-in catalog.

The model build checks coverage of the constructors. The DELETE fixture checks proof search
on symbolic rows, including success and failure boundaries. The laws must also be usable
directly without importing statement execution or automation. This task covers the function
calls in a row expression. Aggregate steps and SQL registration of extension callbacks have
separate execution semantics.
