import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarStrictContractionRateObstruction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# P4-Q2-AJ3: exact Wilson logarithmic rate criterion

AJ1 gives a strictly positive finite-volume deficit mass for the ACTUAL
Wilson centered transfer. AJ2 exhibits why finite-volume strictness alone
cannot imply a spacing-uniform mass.

We now identify the precise missing quantitative statement without
changing the Wilson transfer, top projection, posterior or pair-Haar law.
If every real physical centered-transfer factor q_n is strictly positive,
a COMMON exponential factor bound is equivalent to the SAME lower
bound on the genuine logarithmic rate -log(q_n)/spacing_n.
The possible q_n=0 case is kept in the exponential formulation instead
of assigning log 0 a fictitious finite rate.

No missing physical estimate is asserted. No new axioms, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology
noncomputable section

/-- For any strictly positive contraction family, an all-scales rate
bound is EXACTLY an all-scales exponential one-step bound. -/
theorem p4Q2AJ3_uniformLogRate_iff_uniformExp
    (spacing factor : ℕ → ℝ) (mass : ℝ)
    (hspacing : ∀ n, 0 < spacing n)
    (hfactor : ∀ n, 0 < factor n) :
    (∀ n, mass ≤ -Real.log (factor n) / spacing n) ↔
      (∀ n, factor n ≤ Real.exp (-mass * spacing n)) := by
  constructor
  · intro h n
    exact (p4Q2AI_positiveFactor_spacingRate_iff_exp
      (factor n) (spacing n) mass (hfactor n) (hspacing n)).mp (h n)
  · intro h n
    exact (p4Q2AI_positiveFactor_spacingRate_iff_exp
      (factor n) (spacing n) mass (hfactor n) (hspacing n)).mpr (h n)

/-- Existence of a COMMON positive logarithmic rate is equivalent to
existence of a COMMON positive one-step exponential rate, and does not
follow merely from strictness at each finite scale. -/
theorem p4Q2AJ3_exists_positive_uniformLogRate_iff
    (spacing factor : ℕ → ℝ)
    (hspacing : ∀ n, 0 < spacing n)
    (hfactor : ∀ n, 0 < factor n) :
    (∃ mass : ℝ, 0 < mass ∧
        ∀ n, mass ≤ -Real.log (factor n) / spacing n) ↔
      (∃ mass : ℝ, 0 < mass ∧
        ∀ n, factor n ≤ Real.exp (-mass * spacing n)) := by
  constructor
  · rintro ⟨mass, hmass, h⟩
    exact ⟨mass, hmass,
      (p4Q2AJ3_uniformLogRate_iff_uniformExp spacing factor mass
        hspacing hfactor).mp h⟩
  · rintro ⟨mass, hmass, h⟩
    exact ⟨mass, hmass,
      (p4Q2AJ3_uniformLogRate_iff_uniformExp spacing factor mass
        hspacing hfactor).mpr h⟩

local instance p4AJ3Group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AJ3Compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AJ3SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AJ3Measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AJ3Borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AJ3Complete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- The actual finite-Wilson excited factors (not model/proxy factors):
their uniform logarithmic mass criterion is precisely the common
exponential transfer estimate, when the factors are nonzero. -/
theorem physicalOriginalNormalizedFineTransfer_uniformLogRate_iff
    (halfExtent : ℕ → ℕ) (beta spacing : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (hspacing : ∀ n, 0 < spacing n)
    (hfactor : ∀ n,
      0 < ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta (n+1)) (hbeta (n+1)) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta (n+1)) (hbeta (n+1))‖)
    (mass : ℝ) :
    (∀ n, mass ≤
      -Real.log
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta (n+1)) (hbeta (n+1)) -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta (n+1)) (hbeta (n+1))‖ / spacing n) ↔
    (∀ n,
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta (n+1)) (hbeta (n+1)) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta (n+1)) (hbeta (n+1))‖ ≤ Real.exp (-mass * spacing n)) := by
  exact p4Q2AJ3_uniformLogRate_iff_uniformExp
    spacing
    (fun n =>
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta (n+1)) (hbeta (n+1)) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        (halfExtent (n+1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta (n+1)) (hbeta (n+1))‖)
    mass hspacing hfactor

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
