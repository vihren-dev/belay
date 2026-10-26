import Belay

set_option doc.verso true

/-! Fixture constructors for unresolved view definitions. The explicit helpers exercise
the catalog primitive separately from SQL DDL, through public queries. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

namespace ViewExamples

/-- Extract one SELECT's unresolved syntax. The empty placeholder makes a
non-SELECT fixture fail its later query assertions instead of inventing a view. -/
def definition (script : Script) (columns : Option (List Identifier) := none) : CatalogView :=
  match script.statements.head?.map Prod.fst with
  | some (.select result source joins filter groupBy orderBy limit offset subqueries having distinct compound) =>
    { columns
      query := {
        columns := result, source, joins, filter, groupBy, orderBy,
        limit, offset, having, distinct, compound, parent := none }
      subqueries }
  | none | some (.createTable ..) | some (.createView ..) | some (.createIndex ..) | some (.addColumn ..)
  | some (.dropTable ..) | some (.dropView ..) | some (.dropIndex ..) | some .begin | some .commit | some .rollback
  | some (.insert ..) | some (.insertSelect ..) | some (.update ..) | some (.delete ..) | some (.pragma ..)
  | some (.createTrigger ..) | some (.dropTrigger ..) => {query := commonTablePlaceholder}

/-- Append unresolved definitions with empty storage to a concrete fixture. Each
fixture proves validity of the resulting raw database through the kernel. -/
def withViews (database : Database) (views : List (Identifier × CatalogView)) : Model.Database :=
  views.foldl (fun raw (name, view) => {raw with
    catalog := raw.catalog.createView name view, rows := raw.rows ++ [[]]}) database.raw

/-- The exact native-style prepare message of one statement, or none when
resolution succeeds or stops with a model restriction. -/
def prepareMessage (script : Script) (database : Database) : Option String := do
  let (statement, _) ← script.statements.head?
  match resolveStatement runContext database.raw.connection.resolveState statement with
  | .ok (.prepareError error, _) => some error.message
  | .error _ | .ok (.createTable .., _) | .ok (.createView .., _) | .ok (.createIndex .., _) | .ok (.createTrigger .., _)
  | .ok (.addColumn .., _) | .ok (.drop .., _) | .ok (.begin, _) | .ok (.commit, _)
  | .ok (.rollback, _) | .ok (.insert .., _) | .ok (.insertSelect .., _) | .ok (.update .., _) | .ok (.upsert .., _)
  | .ok (.delete .., _) | .ok (.query .., _) | .ok (.setting .., _) => none

/-- A model restriction retains its SQL use path; successful/native-error
resolutions return none so neither can satisfy a restriction assertion. -/
def restriction (script : Script) (database : Database) : Option NodeRestriction := do
  let (statement, _) ← script.statements.head?
  match resolveStatement runContext database.raw.connection.resolveState statement with
  | .error issue => some issue
  | .ok _ => none

/-- Resolve one SELECT and run it with supplied statement context. This fixture
helper exposes the same clock, counters and bound values to every source. -/
def queryRows (script : Script) (database : Database) (clock : Int) (counters : Counters) :
    Option (List (List Value)) := do
  let (statement, parameters) ← script.statements.head?
  match resolveStatement runContext database.raw.connection.resolveState statement with
  | .ok (.query query subqueries, _) =>
    (query.runOn clock counters parameters database.raw subqueries).map (·.2.rows)
  | .error _ | .ok (.prepareError .., _) | .ok (.createTable .., _) | .ok (.createView .., _) | .ok (.createIndex .., _)
  | .ok (.createTrigger .., _) | .ok (.addColumn .., _) | .ok (.drop .., _) | .ok (.begin, _)
  | .ok (.commit, _) | .ok (.rollback, _) | .ok (.insert .., _) | .ok (.insertSelect .., _) | .ok (.update .., _)
  | .ok (.upsert .., _) | .ok (.delete .., _) | .ok (.setting .., _) => none

/-- Two source rows with distinct numeric/text metadata and an unrelated earlier object. -/
def base : Database := db! r"
  CREATE TABLE earlier(z); CREATE TABLE t(x INTEGER, text_value TEXT COLLATE NOCASE);
  INSERT INTO t VALUES(7,'a'),(8,'b');"

end ViewExamples
