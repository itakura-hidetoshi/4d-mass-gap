import MGAP4D.Audit.ReleaseCounts

namespace MGAP4D
namespace Audit

/-- The release counts satisfy the no-forbidden-token audit condition. -/
structure NoForbiddenTokens where
  noSorry : v16ReleaseCounts.sorryCount = 0
  noAdmit : v16ReleaseCounts.admitCount = 0
  noAxiom : v16ReleaseCounts.axiomCount = 0
  noConstant : v16ReleaseCounts.constantCount = 0

/-- Lean-side record of the v1.6 no-forbidden-token audit. -/
def v16NoForbiddenTokens : NoForbiddenTokens :=
  { noSorry := by rfl,
    noAdmit := by rfl,
    noAxiom := by rfl,
    noConstant := by rfl }

end Audit
end MGAP4D
