import Belay.Sqlite.Model.AdmittedEngineLaws
import Belay.Sqlite.Model.AdmittedRowLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Every profile's admission fact is closed under row deletion and checked admitted writes.
Use this with the row-engine preservation laws when all admission atoms are required.
Proof sketch: combine the existing laws for catalog support, row shape, distinct and bounded
rowids, row width, stored values and rowid aliases. -/
theorem admittedWriteLaws (profile : Profile) : WriteLaws (Database.Admitted profile) where
  sublist database position change facts sub :=
    ⟨(catalogSupportedLaws profile.limits).sublist database position change facts.catalogSupported sub,
     rowsShapedLaws.sublist database position change facts.rowsShaped sub,
     rowidsDistinctFacts.laws.sublist database position change facts.rowidsDistinct sub,
     rowidsInRangeLaws.sublist database position change facts.rowidsInRange sub,
     rowsWideLaws.sublist database position change facts.rowsWide sub,
     rowsStoredLaws.sublist database position change facts.rowsStored sub,
     rowsAliasedLaws.sublist database position change facts.rowsAliased sub⟩
  write database position table rows facts found checked admitted :=
    ⟨(catalogSupportedLaws profile.limits).write database position table rows facts.catalogSupported found checked admitted,
     rowsShapedLaws.write database position table rows facts.rowsShaped found checked admitted,
     rowidsDistinctFacts.laws.write database position table rows facts.rowidsDistinct found checked admitted,
     rowidsInRangeLaws.write database position table rows facts.rowidsInRange found checked admitted,
     rowsWideLaws.write database position table rows facts.rowsWide found checked admitted,
     rowsStoredLaws.write database position table rows facts.rowsStored found checked admitted,
     rowsAliasedLaws.write database position table rows facts.rowsAliased found checked admitted⟩

/-- For any two database properties closed under deletion and checked writes, their
conjunction has the same closure. Proof sketch: apply each supplied law to its conjunct. -/
theorem WriteLaws.and {first second : Database → Prop} (left : WriteLaws first) (right : WriteLaws second) :
    WriteLaws (fun database => first database ∧ second database) where
  sublist database position change facts sub :=
    ⟨left.sublist database position change facts.1 sub, right.sublist database position change facts.2 sub⟩
  write database position table rows facts found checked admitted :=
    ⟨left.write database position table rows facts.1 found checked admitted,
     right.write database position table rows facts.2 found checked admitted⟩

end Belay.Sqlite.Model
