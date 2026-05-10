import MGAP4D.Global.Concrete.SummarySurface
import MGAP4D.ReplacementPass2

namespace MGAP4D
namespace Global
namespace Concrete

structure GlobalConcretePass2Bundle where
  summaryReady : Prop
  workUnitSummaryReady : Prop
  replacementReady : Prop
  pass2GateReady : Prop
  statusPreserved : Prop

def GlobalConcretePass2Bundle.ready (B : GlobalConcretePass2Bundle) : Prop :=
  B.summaryReady ∧ B.workUnitSummaryReady ∧ B.replacementReady ∧
  B.pass2GateReady ∧ B.statusPreserved

theorem global_concrete_pass2_bundle_pack
    (B : GlobalConcretePass2Bundle) :
    B.ready ↔ B.summaryReady ∧ B.workUnitSummaryReady ∧ B.replacementReady ∧
      B.pass2GateReady ∧ B.statusPreserved := by
  rfl

end Concrete
end Global
end MGAP4D
