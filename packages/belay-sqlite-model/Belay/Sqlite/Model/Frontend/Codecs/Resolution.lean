import Belay.Sqlite.Model.Frontend.Codecs.SyntaxJson
import Belay.Sqlite.Model.Values.Json.Resolution

set_option doc.verso true

namespace Belay.Sqlite.Model

deriving instance Lean.ToJson for DependentKind
deriving instance Lean.ToJson for DependentPhase

-- One command per type: a combined `deriving instance` treats its types as one group.
deriving instance Lean.ToExpr for Comparison
deriving instance Lean.ToExpr for ArithmeticOperator
deriving instance Lean.ToExpr for CompoundOperator
deriving instance Lean.ToExpr for Affinity
deriving instance Lean.ToExpr for ConflictAlgorithm
deriving instance Lean.ToExpr for CounterKind
deriving instance Lean.ToExpr for Syntax.QuoteKind
deriving instance Lean.ToExpr for Syntax.NameToken
deriving instance Lean.ToExpr for Syntax.SourceText
deriving instance Lean.ToExpr for Syntax.RaiseKind
deriving instance Lean.ToExpr for Syntax.Expr
deriving instance Lean.ToExpr for Syntax.ResultColumn
deriving instance Lean.ToExpr for Syntax.OrderTerm
deriving instance Lean.ToExpr for Syntax.DefaultExpression
deriving instance Lean.ToExpr for Syntax.ForeignKeyAction
deriving instance Lean.ToExpr for Syntax.ColumnConstraint
deriving instance Lean.ToExpr for Syntax.ColumnDefinition
deriving instance Lean.ToExpr for Syntax.TableConstraint
deriving instance Lean.ToExpr for Syntax.TableReference
deriving instance Lean.ToExpr for Syntax.Join
deriving instance Lean.ToExpr for Syntax.Compound
deriving instance Lean.ToExpr for Syntax.CommonTable
deriving instance Lean.ToExpr for Syntax.Subquery
deriving instance Lean.ToExpr for Syntax.SelectBody
deriving instance Lean.ToExpr for Syntax.ConflictAction
deriving instance Lean.ToExpr for Syntax.ConflictClause
deriving instance Lean.ToExpr for Syntax.TableOptions
deriving instance Lean.ToExpr for Syntax.TriggerTime
deriving instance Lean.ToExpr for Syntax.TriggerEvent
deriving instance Lean.ToExpr for Syntax.BodyStatement
deriving instance Lean.ToExpr for Syntax.PragmaSetting
deriving instance Lean.ToExpr for Syntax.Pragma
deriving instance Lean.ToExpr for Syntax.Statement

deriving instance Lean.ToExpr for TimeKeyword
deriving instance Lean.ToExpr for DefaultInsert
deriving instance Lean.ToExpr for DefaultForm
deriving instance Lean.ToExpr for ColumnDefault
deriving instance Lean.ToExpr for Collation

deriving instance Lean.ToExpr for Resolved.DateFunction
deriving instance Lean.ToExpr for Resolved.TrimSide
deriving instance Lean.ToExpr for Resolved.ScalarFunction
deriving instance Lean.ToExpr for Resolved.Expr, Resolved.Arguments
deriving instance Lean.ToExpr for LabelTarget
deriving instance Lean.ToExpr for LabelName
deriving instance Lean.ToExpr for CheckText
deriving instance Lean.ToExpr for CheckConstraint
deriving instance Lean.ToExpr for ForeignKey
deriving instance Lean.ToExpr for GeneratedColumn
deriving instance Lean.ToExpr for StrictType
deriving instance Lean.ToExpr for CatalogColumn
deriving instance Lean.ToExpr for CatalogTable
deriving instance Lean.ToExpr for KeyTerm
deriving instance Lean.ToExpr for IndexKey
deriving instance Lean.ToExpr for CatalogIndex
deriving instance Lean.ToExpr for CatalogTrigger
deriving instance Lean.ToExpr for CatalogView
deriving instance Lean.ToExpr for CatalogEntry
deriving instance Lean.ToExpr for CatalogObject
deriving instance Lean.ToExpr for Database

deriving instance Lean.ToExpr for DependentKind
deriving instance Lean.ToExpr for DependentPhase

deriving instance Lean.ToExpr for Resolved.Aggregate
deriving instance Lean.ToExpr for Resolved.Output
deriving instance Lean.ToExpr for Resolved.SortKey
deriving instance Lean.ToExpr for Resolved.SortTerm
deriving instance Lean.ToExpr for Resolved.JoinKind
deriving instance Lean.ToExpr for Resolved.PragmaRows
deriving instance Lean.ToExpr for Resolved.Source
deriving instance Lean.ToExpr for Resolved.QuerySource
deriving instance Lean.ToExpr for Resolved.Compound
deriving instance Lean.ToExpr for Resolved.Query
deriving instance Lean.ToExpr for Resolved.ConflictAction
deriving instance Lean.ToExpr for Resolved.ConflictClause
deriving instance Lean.ToExpr for Resolved.ConflictPolicy
deriving instance Lean.ToExpr for Resolved.Cell
deriving instance Lean.ToExpr for Resolved.SourceCell
deriving instance Lean.ToExpr for Resolved.TriggerEvent
deriving instance Lean.ToExpr for Resolved.Step
deriving instance Lean.ToExpr for Resolved.Program
deriving instance Lean.ToExpr for Resolved.WriteRules

end Belay.Sqlite.Model
