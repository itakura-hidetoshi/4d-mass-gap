import MGAP4D.OperatorAPI.WorkUnitChainExecutionReady
import MGAP4D.OperatorAPI.TheoremSurface
import MGAP4D.OperatorAPI.ReplacementReady
import MGAP4D.ReplacementPass2

namespace MGAP4D
namespace OperatorAPI

structure OperatorAPIPass2Bundle where
  workUnitReady : Prop
  theoremSurfaceReady : Prop
  replacementReady : Prop
  pass2GateReady : Prop
  statusPreserved : Prop

def OperatorAPIPass2Bundle.ready (B : OperatorAPIPass2Bundle) : Prop :=
  B.workUnitReady ∧ B.theoremSurfaceReady ∧ B.replacementReady ∧
  B.pass2GateReady ∧ B.statusPreserved

theorem operator_api_pass2_bundle_pack
    (B : OperatorAPIPass2Bundle) :
    B.ready ↔ B.workUnitReady ∧ B.theoremSurfaceReady ∧ B.replacementReady ∧
      B.pass2GateReady ∧ B.statusPreserved := by
  rfl

end OperatorAPI
end MGAP4D
