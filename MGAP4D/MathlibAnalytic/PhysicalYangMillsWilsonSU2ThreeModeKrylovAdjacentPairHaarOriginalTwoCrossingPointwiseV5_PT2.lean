import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWeightedCrossingGaugeWardV5_PT
import Mathlib.Tactic

/-!
# P4-Q2-PT2 — pointwise original Wilson two-crossing residual decomposition

The original PS stripped action includes W(A)/2 and the real
temporal crossing action, without changing the physical model.
This step decomposes the exact original integrand into spatial,
single-crossing and two-crossing contributions. The single-crossing
weight is exactly the gauge-invariant weight proved in PT.
No assertion that the two-crossing Haar moment vanishes is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PT2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PT2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PT2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PT2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PT2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalTwoCrossingPointwise
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "k" => p4Q2PT_originalSingleCrossingWardWeight H

noncomputable def p4Q2PT2_originalTwoCrossingCenteredHaar (B : Cfg) : ℝ :=
  ∫ A : Cfg, (Cross A B) ^ 2 * h A ∂haar

/-- Exact pointwise expansion in the unchanged original Wilson action. -/
theorem p4Q2PT2_originalWardIntegrand_crossingExpansion
    (A B : Cfg) :
    (p4Q2PS_originalRightStrippedAction H A B) ^ 2 * h A -
      p4Q2PS_originalRightStrippedAction H A B * b A =
    ((w A) ^ 2 * h A - w A * b A) +
      k A * Cross A B + (Cross A B) ^ 2 * h A := by
  unfold p4Q2PS_originalRightStrippedAction
    p4Q2PT_originalSingleCrossingWardWeight
  ring

end OriginalTwoCrossingPointwise
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT2_originalWardIntegrand_crossingExpansion
