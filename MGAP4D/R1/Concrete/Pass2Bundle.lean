import MGAP4D.R1.Concrete.ClosureTargetsStatus
import MGAP4D.R1.TheoremSurface
import MGAP4D.ReplacementPass2

namespace MGAP4D
namespace R1
namespace Concrete

structure R1ClosurePass2Bundle where
  closureStatusReady : Prop
  r1SurfaceReady : Prop
  replacementReady : Prop
  pass2GateReady : Prop
  statusPreserved : Prop

def R1ClosurePass2Bundle.ready (B : R1ClosurePass2Bundle) : Prop :=
  B.closureStatusReady ∧ B.r1SurfaceReady ∧ B.replacementReady ∧
  B.pass2GateReady ∧ B.statusPreserved

theorem r1_closure_pass2_bundle_pack
    (B : R1ClosurePass2Bundle) :
    B.ready ↔ B.closureStatusReady ∧ B.r1SurfaceReady ∧ B.replacementReady ∧
      B.pass2GateReady ∧ B.statusPreserved := by
  rfl

end Concrete
end R1
end MGAP4D
