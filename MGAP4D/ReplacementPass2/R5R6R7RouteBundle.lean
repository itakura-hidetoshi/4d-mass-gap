import MGAP4D.R5.Concrete.ExportStatus
import MGAP4D.R6.Concrete.ExportStatus
import MGAP4D.R7.Concrete.ExactGapStatus
import MGAP4D.R5.TheoremSurface
import MGAP4D.R6.TheoremSurface
import MGAP4D.R7.TheoremSurface
import MGAP4D.ReplacementPass2

namespace MGAP4D
namespace ReplacementPass2

structure R5R6R7RoutePass2Bundle where
  r5ExportReady : Prop
  r6ExportReady : Prop
  r7ExactReady : Prop
  r5SurfaceReady : Prop
  r6SurfaceReady : Prop
  r7SurfaceReady : Prop
  pass2GateReady : Prop
  statusPreserved : Prop

def R5R6R7RoutePass2Bundle.ready (B : R5R6R7RoutePass2Bundle) : Prop :=
  B.r5ExportReady ∧ B.r6ExportReady ∧ B.r7ExactReady ∧
  B.r5SurfaceReady ∧ B.r6SurfaceReady ∧ B.r7SurfaceReady ∧
  B.pass2GateReady ∧ B.statusPreserved

theorem r5_r6_r7_route_pass2_bundle_pack
    (B : R5R6R7RoutePass2Bundle) :
    B.ready ↔ B.r5ExportReady ∧ B.r6ExportReady ∧ B.r7ExactReady ∧
      B.r5SurfaceReady ∧ B.r6SurfaceReady ∧ B.r7SurfaceReady ∧
      B.pass2GateReady ∧ B.statusPreserved := by
  rfl

end ReplacementPass2
end MGAP4D
