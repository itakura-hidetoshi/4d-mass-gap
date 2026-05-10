import MGAP4D.OperatorAPI.PhasePlan

namespace MGAP4D
namespace OperatorAPI

structure Phase1Targets where
  r1RouteReady : Prop
  r1ProjectionReady : Prop
  r2ReducingReady : Prop
  r5SpectrumSurfaceReady : Prop

def Phase1Targets.ready (T : Phase1Targets) : Prop :=
  T.r1RouteReady ∧ T.r1ProjectionReady ∧ T.r2ReducingReady ∧ T.r5SpectrumSurfaceReady

theorem phase1_targets_pack
    (T : Phase1Targets) :
    T.ready ↔ T.r1RouteReady ∧ T.r1ProjectionReady ∧ T.r2ReducingReady ∧ T.r5SpectrumSurfaceReady := by
  rfl

end OperatorAPI
end MGAP4D
