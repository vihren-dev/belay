import Belay.Sqlite.Model.Queries.Preparation.RestrictionText
import Belay.Sqlite.Model.Shared.Resolved.Resolved
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic

open Lean

namespace Belay.Sqlite.Model.Conformance

/-- The prediction of a model restriction: the case is out of scope, with the reason and the
kind of the restriction. -/
def restrictedJson (restriction : Restriction) : Json :=
  Json.mkObj [("restricted", toJson restriction.reason), ("restriction", toJson restriction.kind.id)]

end Belay.Sqlite.Model.Conformance
