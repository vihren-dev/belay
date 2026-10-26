module

set_option doc.verso true

/-! This module is selected explicitly; the main dependency fixture does not import it. -/

namespace Standalone

/-- A declaration outside the fixture's import closure still belongs in the report. -/
public theorem selectedSeparately : True := True.intro

end Standalone
