import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredGIReceiverTranslationV5_PZ37AAU2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorSpatialHaarTransportV5_PZ37AAQ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAU3 — unconditional true original Wilson posterior participation

AAU2 gives pointwise exact translation covariance of the original centered
Gauss-law two-Wilson-posterior signed GI expectation gap; AAT proves the exact
translation covariance of the original FX conditional density-contrast Haar-L²
variance. AAQ supplies original pair-Haar invariance and its precise quotient
integration bridge. Discharge AAP's ORIGINAL posterior response covariance
without a new hypothesis. Apply the already proved genuine AAP finite-link
orbit bounds, with the original three spatial directions:

  M₂(H,b) ≤ 3 R(H,b)²,
  P(H,b) ≥ 1/3,

and half-Rayleigh active-link density ≥ 1/12 for EVERY finite H and b>0.

These are genuine fixed-β posterior nonconcentration/participation estimates,
NOT a uniform positive Rayleigh or coercivity floor, common fine interval,
endpoint E/F, H1–H4, or continuum Yang–Mills mass gap.
All original Wilson kernel, Haar, physical source and Gauss-law structures
are unchanged; append-only, no axioms/sorry/admit/native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAU3_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAU3_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAU3_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAU3_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAU3_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section UnconditionalOriginalWilsonParticipation
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H

/-- The PREVIOUSLY CONDITIONAL AAP genuine ORIGINAL two-interacting
Wilson-posterior link-response covariance now holds unconditionally. -/
theorem p4Q2PZ37AAU_originalPosteriorSpatialTranslationCovariant
    (b : ℝ) (hb : 0 < b) :
    p4Q2PZ37AAP_originalPosteriorSpatialTranslationCovariant H b hb := by
  apply p4Q2PZ37AAQ_originalPosteriorCovariance_of_gap_and_variance H b hb
  · intro a e z
    exact p4Q2PZ37AAU_originalCenteredPhysicalGIGap_translation
      H a b hb.le e z
  · intro a e z
    exact p4Q2PZ37AAT_originalPosteriorContrastVariance_spatialTranslation
      H a b hb.le z.2 e

/-- Genuine original Wilson posterior second moment obeys a
volume-independent relative cap without conditional symmetry hypotheses. -/
theorem p4Q2PZ37AAU_originalSecondMoment_le_threeRayleighSq
    (b : ℝ) (hb : 0 < b) :
    p4Q2PZ37AAN_originalPosteriorLinkSecondMoment H b hb ≤
      3 * (p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)^2 := by
  exact p4Q2PZ37AAP_covariance_implies_originalSecondMomentBound
    H b hb (p4Q2PZ37AAU_originalPosteriorSpatialTranslationCovariant H b hb)

/-- ORIGINAL interacting Wilson-posterior effective spatial-link
participation is at least one third at every finite volume and β>0. -/
theorem p4Q2PZ37AAU_originalParticipation_ge_oneThird
    (b : ℝ) (hb : 0 < b) :
    (1 / 3 : ℝ) ≤
      p4Q2PZ37AAO_originalPosteriorParticipationFraction H b hb := by
  exact p4Q2PZ37AAP_covariance_implies_originalParticipation_third
    H b hb (p4Q2PZ37AAU_originalPosteriorSpatialTranslationCovariant H b hb)

/-- At least one twelfth of the ORIGINAL spatial links have genuine
posterior response above the half-Rayleigh average threshold.
No uniform positive lower bound on that threshold is claimed. -/
theorem p4Q2PZ37AAU_originalHalfRayleighActiveLinks_ge_oneTwelfth
    (b : ℝ) (hb : 0 < b) :
    ((1 / 12 : ℝ) * (Fintype.card Link : ℝ)) ≤
      ((p4Q2PZ37AAL_originalActiveLinks H b hb
        ((1 / 2 : ℝ) *
          p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)).card : ℝ) := by
  exact p4Q2PZ37AAP_covariance_implies_halfRayleighActiveDensity
    H b hb (p4Q2PZ37AAU_originalPosteriorSpatialTranslationCovariant H b hb)

end UnconditionalOriginalWilsonParticipation
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalPosteriorSpatialTranslationCovariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalSecondMoment_le_threeRayleighSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalParticipation_ge_oneThird
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAU_originalHalfRayleighActiveLinks_ge_oneTwelfth
