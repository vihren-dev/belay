import Belay.Sqlite.Model.ForeignKeyFacts

set_option doc.verso true

/-! Frame laws for parent-schema compatibility. They track parent definitions and ordered
eligible indexes independently of stored rows. -/

namespace Belay.Sqlite.Model

/-- The catalog inputs used to select one declaration's parent: the named parent has the
same position and definition, or is absent in both catalogs; when present, its eligible
indexes, including their order, agree. When no physical parent exists, the named view
has the same position or is absent in both catalogs. View bodies and stored rows are unrestricted. -/
structure ForeignKey.ParentSchemaFrame (key : ForeignKey) (before after : Catalog) : Prop where
  /-- The named parent has the same position and definition, or is absent in both catalogs. -/
  parent : after.findTable key.table = before.findTable key.table
  /-- Every parent found by the old catalog has the same ordered eligible indexes afterward. -/
  indexes : ∀ position shape, before.findTable key.table = some (position, shape) →
    after.parentIndexes position shape = before.parentIndexes position shape
  /-- Without a physical parent, both catalogs find the same view position or no view.
  Its definition can change. A present physical parent imposes no condition here. -/
  viewPosition : before.findTable key.table = none →
    (after.findView key.table).map Prod.fst = (before.findView key.table).map Prod.fst

/-- For every declaration and parent-schema frame, the catalogs select the same parent link.
Proof sketch: the parent definition gives rowid and named columns, and equal eligible indexes
make the existing parent-key selector return the same key. Without a physical parent,
the view-position equality preserves the missing or mismatched link. -/
theorem ForeignKey.ParentSchemaFrame.parentLink {key : ForeignKey} {before after : Catalog}
    (frame : key.ParentSchemaFrame before after) : after.parentLink key = before.parentLink key := by
  unfold Catalog.parentLink
  rw [frame.parent]
  cases found : before.findTable key.table with
  | none =>
    have views := frame.viewPosition found
    cases old : before.findView key.table <;> cases new : after.findView key.table <;> simp_all
  | some pair =>
    rcases pair with ⟨position, shape⟩
    have indexes := frame.indexes position shape found
    have selected : after.parentKey position shape key = before.parentKey position shape key := by
      simp only [Catalog.parentKey, indexes]
    simp only [selected]

/-- A table schema fact transfers when every new declaration is an old declaration, the
supplied parent mapping agrees for each one, and its named-parent definition, eligible indexes and absent-parent view position
are unchanged. Stored child and parent rows are unrestricted. -/
structure Table.ParentSchemaFrame (before after : Catalog) (oldMapping newMapping : ForeignKeyMapping)
    (oldPosition position : Nat) (oldTable table : Table) : Prop where
  /-- Each new declaration already occurs in the old table. -/
  declarations : ∀ key ∈ table.shape.allForeignKeys, key ∈ oldTable.shape.allForeignKeys
  /-- Each new declared mapping agrees with the corresponding old mapping. -/
  mapping : ∀ key ∈ table.shape.allForeignKeys,
    newMapping.parent position key = oldMapping.parent oldPosition key
  /-- Each new declaration has the same parent-definition, eligible-index and absent-parent view-position inputs. -/
  parents : ∀ key ∈ table.shape.allForeignKeys, key.ParentSchemaFrame before after

/-- For every table parent-schema fact and frame, the new table has that fact. Its stored
rows may all change. Proof sketch: copy each located mapping and its catalog-selection equality
through the corresponding parent-schema frame. -/
theorem Table.ParentSchemasCompatible.frame {before after : Catalog} {oldMapping newMapping : ForeignKeyMapping}
    {oldPosition position : Nat} {oldTable table : Table}
    (holds : oldTable.ParentSchemasCompatible oldMapping before oldPosition)
    (frame : Table.ParentSchemaFrame before after oldMapping newMapping oldPosition position oldTable table) :
    table.ParentSchemasCompatible newMapping after position := by
  intro key declared
  rw [frame.mapping key declared, (frame.parents key declared).parentLink]
  exact holds key (frame.declarations key declared)

/-- If every target table has a parent-schema frame from a source table and the source database
has compatible parent schemas, the target does too. Proof sketch: apply the table law at every
target table; neither frame nor schema fact reads stored rows. -/
theorem Database.ParentSchemasCompatible.frame {before after : Database} {oldMapping newMapping : ForeignKeyMapping}
    (holds : before.ParentSchemasCompatible oldMapping)
    (frames : ∀ position table, after.table position = some table →
      ∃ oldPosition oldTable, before.table oldPosition = some oldTable ∧
        Table.ParentSchemaFrame before.catalog after.catalog oldMapping newMapping oldPosition position oldTable table) :
    after.ParentSchemasCompatible newMapping := by
  intro position table present
  obtain ⟨oldPosition, oldTable, found, frame⟩ := frames position table present
  exact (holds oldPosition oldTable found).frame frame

/-- For every two databases with the same catalog, any compatible supplied mapping for the
first is compatible for the second, regardless of their rows. Proof sketch: each table in the
second has the same definition in the first, and schema compatibility reads only that definition.
-/
theorem Database.ParentSchemasCompatible.catalog_eq {before after : Database} {mapping : ForeignKeyMapping}
    (holds : before.ParentSchemasCompatible mapping) (same : after.catalog = before.catalog) :
    after.ParentSchemasCompatible mapping := by
  intro position table present key declared
  obtain ⟨shape, atShape, equal⟩ := Option.map_eq_some_iff.mp present
  subst table
  have found : before.table position = some { shape, rows := before.rows.getD position [] } := by
    simp only [Database.table, ← same, atShape, Option.map_some]
  simpa only [same] using holds position _ found key declared

end Belay.Sqlite.Model
