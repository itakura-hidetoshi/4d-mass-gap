import MGAP4D.MathlibAdoptionGate.MainAdoptionHoldDecision
import MGAP4D.R3.Theorem
import MGAP4D.R4.Theorem
import MGAP4D.R5.Theorem
import MGAP4D.R6.Theorem
import MGAP4D.R7.Theorem

namespace MGAP4D

structure PostMathlibHoldTheoremHardening where
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  dryRunBuildabilityNotTheoremCompletion : Prop
  r3ShiftedZeroFormRouteDeferred : Prop
  r4LowerBoundRouteDeferred : Prop
  r5SpectrumInfimumRouteDeferred : Prop
  r6IntervalExclusionRouteDeferred : Prop
  r7AtomExactGapRouteDeferred : Prop
  theoremRouteHardeningContinues : Prop
  publicBoundaryHeld : Prop

def PostMathlibHoldTheoremHardening.ready (H : PostMathlibHoldTheoremHardening) : Prop :=
  H.mainPreMathlib ∧ H.mathlibMainAdoptionHeld ∧
  H.dryRunBuildabilityNotTheoremCompletion ∧ H.r3ShiftedZeroFormRouteDeferred ∧
  H.r4LowerBoundRouteDeferred ∧ H.r5SpectrumInfimumRouteDeferred ∧
  H.r6IntervalExclusionRouteDeferred ∧ H.r7AtomExactGapRouteDeferred ∧
  H.theoremRouteHardeningContinues ∧ H.publicBoundaryHeld

theorem post_mathlib_hold_theorem_hardening_pack (H : PostMathlibHoldTheoremHardening) :
    H.ready ↔ H.mainPreMathlib ∧ H.mathlibMainAdoptionHeld ∧
      H.dryRunBuildabilityNotTheoremCompletion ∧ H.r3ShiftedZeroFormRouteDeferred ∧
      H.r4LowerBoundRouteDeferred ∧ H.r5SpectrumInfimumRouteDeferred ∧
      H.r6IntervalExclusionRouteDeferred ∧ H.r7AtomExactGapRouteDeferred ∧
      H.theoremRouteHardeningContinues ∧ H.publicBoundaryHeld := by
  rfl

end MGAP4D
