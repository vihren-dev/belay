# belay-sqlite-model

The Lean model of SQLite that the verifier checks migrations against: name resolution
(`Belay/Sqlite/Model/Resolution/`), the executable model of statements and scripts
(`Belay/Sqlite/Model/`), and the codec (`Belay/Sqlite/Model/Codec/`).

## File names

The suffix of a file name tells what the file holds:

| Suffix | Contents |
| --- | --- |
| `Laws` | Theorems about the executable model, such as `StoreValueLaws.lean` or `PreservationLaws.lean`. |
| `Spec` | Theorems about name resolution, such as `PrepareSpec.lean` or `RowSpec.lean`. |
| `Examples` | Checked examples (`#guard`, `example`) of the model or of resolution. |

A file without one of these suffixes holds definitions. It can also hold the theorems
about those definitions that other definitions in the same file need.
