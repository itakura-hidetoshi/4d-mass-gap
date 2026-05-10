import MGAP4D.R2.Concrete.ExportStatus
import MGAP4D.R4.Concrete.ExportStatus
import MGAP4D.R3.Concrete.ExportStatus
import MGAP4D.R2.TheoremSurface
import MGAP4D.R4.TheoremSurface
import MGAP4D.R3.TheoremSurface
import MGAP4D.ReplacementPass2

namespace MGAP4D
namespace ReplacementPass2

structure R2R4R3RoutePass2Bundle where
  r2ExportReady : Prop
  r4ExportReady : Prop
  r3ExportReady : Prop
  r2SurfaceReady : Prop
  r4SurfaceReady : Prop
  r3SurfaceReady : Prop
  pass2GateReady : Prop
  statusPreserved : Prop

def R2R4R3RoutePass2Bundle.ready (B : R2R4R3RoutePass2Bundle) : Prop :=
  B.r2ExportReady ∧ B.r4ExportReady ∧ B.r3ExportReady ∧
  B.r2SurfaceReady ∧ B.r4SurfaceReady ∧ B.r3SurfaceReady ∧
  B.pass2GateReady ∧ B.statusPreserved

theorem r2_r4_r3_route_pass2_bundle_pack
    (B : R2R4R3RoutePass2Bundle) :
    B.ready ↔ B.r2ExportReady ∧ B.r4ExportReady ∧ B.r3ExportReady ∧
      B.r2SurfaceReady ∧ B.r4SurfaceReady ∧ B.r3SurfaceReady ∧
      B.pass2GateReady ∧ B.statusPreserved := by
  rfl

end ReplacementPass2
end MGAP4D
