import MGAP4D.PostMathlibHoldTheoremHardening
import MGAP4D.R3.Theorem
import MGAP4D.R4.Theorem
import MGAP4D.R5.Theorem
import MGAP4D.R6.Theorem
import MGAP4D.R7.Theorem

namespace MGAP4D

structure R3R7RouteSpecificHardening where
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  r3RouteHardeningVisible : Prop
  r4RouteHardeningVisible : Prop
  r5RouteHardeningVisible : Prop
  r6RouteHardeningVisible : Prop
  r7RouteHardeningVisible : Prop
  r3StillDeferred : Prop
  r4StillDeferred : Prop
  r5StillDeferred : Prop
  r6StillDeferred : Prop
  r7StillDeferred : Prop
  publicBoundaryHeld : Prop

def R3R7RouteSpecificHardening.ready (H : R3R7RouteSpecificHardening) : Prop :=
  H.mainPreMathlib ∧ H.mathlibMainAdoptionHeld ∧
  H.r3RouteHardeningVisible ∧ H.r4RouteHardeningVisible ∧
  H.r5RouteHardeningVisible ∧ H.r6RouteHardeningVisible ∧ H.r7RouteHardeningVisible ∧
  H.r3StillDeferred ∧ H.r4StillDeferred ∧ H.r5StillDeferred ∧
  H.r6StillDeferred ∧ H.r7StillDeferred ∧ H.publicBoundaryHeld

theorem r3_r7_route_specific_hardening_pack (H : R3R7RouteSpecificHardening) :
    H.ready ↔ H.mainPreMathlib ∧ H.mathlibMainAdoptionHeld ∧
      H.r3RouteHardeningVisible ∧ H.r4RouteHardeningVisible ∧
      H.r5RouteHardeningVisible ∧ H.r6RouteHardeningVisible ∧ H.r7RouteHardeningVisible ∧
      H.r3StillDeferred ∧ H.r4StillDeferred ∧ H.r5StillDeferred ∧
      H.r6StillDeferred ∧ H.r7StillDeferred ∧ H.publicBoundaryHeld := by
  rfl

end MGAP4D
