import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorFXCapFromFKV5_PZ37ABA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABA2 — genuine original GI unweighted moment is positive
at every fixed finite volume and frozen b>0

Combine AAZ's UNCONDITIONAL non-a.e.-zero detection on one actual link
with ABA's independently reconstructed FK original-FX variance envelope
and AAZ2's automatic integrability for the same original source.

The authentic full outer pair-Haar integral
  G_(H,b,e) = integral_pairHaar |Delta_(H,b,e)(z)|^2
is then STRICTLY POSITIVE for some actual spatial link e at EACH
fixed H,b>0, as a genuine finite value. This is stronger than a
pointwise/non-a.e.-zero witness but does NOT yield a positive infimum
over H nor construct a volume-independent positive-measure cylinder.

No changed center, two interacting posteriors, Gauss-law source,
Wilson kernel or original pair-Haar. No new axioms/sorry/admit/
native_decide, conditional density surrogate, or continuum claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABA2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABA2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABA2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABA2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABA2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- For every original finite-volume interacting Wilson model at
b>0, at least one genuine link has a FINITE and strictly positive
unweighted expectation-gap square moment on the full original
boundary pair-Haar law. No uniform m>0 is asserted. -/
theorem p4Q2PZ37ABA2_exists_originalLink_positiveUnweightedGIMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      0 < p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  obtain ⟨e, hNotAE⟩ :=
    p4Q2PZ37AAZ_exists_originalLink_centeredGIGap_notAEZero H b hb
  refine ⟨e, ?_⟩
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let D : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let F : Pair → ℝ := fun z => (D z)^2
  have hQCap : ∀ z : Pair,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e ≤
        (Real.exp (16 * b) - Real.exp (-16 * b)) ^ 2 := by
    intro z
    exact p4Q2PZ37ABA_originalFXVariance_le_FK_envelope
      H b hb.le z.2 e
  have hFInt : Integrable F μ := by
    change Integrable
      (fun z : Pair =>
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
    exact p4Q2PZ37AAZ2_originalUnweightedGIGapSquare_integrable_of_FXCap
      H b hb e ((Real.exp (16 * b) - Real.exp (-16 * b)) ^ 2) hQCap
  have hNotAED : ¬ (∀ᵐ z ∂μ, D z = 0) := by
    exact hNotAE
  have hNotAEF : ¬ (F =ᵐ[μ] (0 : Pair → ℝ)) := by
    intro hAEF
    apply hNotAED
    filter_upwards [hAEF] with z hz
    exact (sq_eq_zero_iff).mp hz
  have hSupportNeZero : μ (Function.support F) ≠ 0 := by
    intro hZero
    exact hNotAEF ((Measure.measure_support_eq_zero_iff μ).mp hZero)
  have hSupportPos : 0 < μ (Function.support F) :=
    pos_iff_ne_zero.mpr hSupportNeZero
  have hNonneg : ∀ z : Pair, 0 ≤ F z := fun z => sq_nonneg _
  change 0 < ∫ z, F z ∂μ
  exact (integral_pos_iff_support_of_nonneg hNonneg hFInt).mpr hSupportPos

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABA2_exists_originalLink_positiveUnweightedGIMoment
