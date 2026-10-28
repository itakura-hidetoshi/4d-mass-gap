import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRetainedLinkDensityPosteriorFloorV5_PZ37AAL
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAM — original posterior link cap and retained-response count

The AAK normalized centered Wilson physical Rayleigh is the exact
sum of TRUE two-interacting-Wilson-posterior GL contributions j_(H,b,e)
over ALL original spatial links. The new input here is ZC's
source-norm bound on the SAME original single-link full-pair-Haar
posterior expectation gap divided by its actual positive variance.

Because AAJ proved C_H=4*||V_H||²>0, each original normalized
posterior link response obeys the *genuine* upper bound

  0 <= j_(H,b,e) <= 2 / exp(-16*b).

This upper cap is independent of H at fixed b but is of order ONE
per link, NOT the 1/|Links_H| bound needed to force positive active
link DENSITY by averaging. The retained response of ANY genuine
spatial-link subset S is at most |S|*2/exp(-16*b).

Thus if S alone carries source-normalized posterior Rayleigh
response at least c, necessarily

  |S| >= c*exp(-16*b)/2.

A retained-link fraction assumption is strictly more demanding than
this O(1) count condition as the link count grows. Neither this result
nor the existing AAL sufficient condition proves an all-volume lower
Rayleigh bound. No posterior/source is replaced; no E/F/H1-H4 or
continuum Yang–Mills gap, new axioms, sorry/admit/native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAM_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- TRUE, not surrogate, two-interacting-posterior single-link normalized
physical Wilson response is bounded by the ORIGINAL ZC Hilbert-source
estimate. In particular the upper cap does NOT decay with volume. -/
theorem p4Q2PZ37AAM_originalNormalizedLinkResponse_le_explicitPosteriorCap
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e ≤
      2 / Real.exp (-16 * b) := by
  let V := p4Q2PZ37ZW_originalCenteredPhysicalDirection H
  let C := p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H
  let J := p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e
  let E := Real.exp (-16 * b)
  have hE : 0 < E := Real.exp_pos _
  have hC : 0 < C := p4Q2PZ37AAJ_originalHaarCovariance_pos H
  have hCnorm : C = 4 * ‖V‖^2 := by
    have h := p4Q2PZ37AAJ_originalPhysicalNorm_sq_eq_quarterHaarCovariance H
    change ‖V‖^2 = (1 / 4 : ℝ) * C at h
    linarith
  have hJ : J ≤ (2 * ‖V‖^2) / E := by
    simpa only [
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass,
      p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse,
      Finset.sum_singleton, Finset.card_singleton,
      Nat.cast_one, one_mul] using
      (p4Q2PZ37ZC_originalGL_patch_le_explicit_physicalSourceNorm
        H b hb V ({e} : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
  have hJE : J * E ≤ 2 * ‖V‖^2 :=
    (le_div_iff₀ hE).mp hJ
  change (4 * J) / C ≤ 2 / E
  apply (div_le_div_iff₀ hC hE).mpr
  rw [hCnorm]
  nlinarith

/-- Every actual subset of original Wilson links has true normalized
posterior response at most its literal cardinality times the
single-link H-independent (at frozen b) cap. -/
theorem p4Q2PZ37AAM_originalRetainedResponse_le_card_posteriorCap
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2PZ37AAL_originalRetainedLinkRayleigh H b hb S ≤
      (S.card : ℝ) * (2 / Real.exp (-16 * b)) := by
  classical
  unfold p4Q2PZ37AAL_originalRetainedLinkRayleigh
  calc
    (∑ e ∈ S, p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e) ≤
        ∑ _e ∈ S, (2 / Real.exp (-16 * b)) :=
      Finset.sum_le_sum (fun e _he =>
        p4Q2PZ37AAM_originalNormalizedLinkResponse_le_explicitPosteriorCap
          H b hb e)
    _ = (S.card : ℝ) * (2 / Real.exp (-16 * b)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Even if a retained original link subset captures c>0 of the
ACTUAL centered physical Rayleigh, the original per-link cap only
forces a NUMBER of links, not a positive all-volume density. -/
theorem p4Q2PZ37AAM_retained_response_floor_forces_linkCount
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (c : ℝ)
    (hCapture : c ≤ p4Q2PZ37AAL_originalRetainedLinkRayleigh H b hb S) :
    c * Real.exp (-16 * b) / 2 ≤ (S.card : ℝ) := by
  have hE : 0 < Real.exp (-16 * b) := Real.exp_pos _
  have hCap := hCapture.trans
    (p4Q2PZ37AAM_originalRetainedResponse_le_card_posteriorCap H b hb S)
  have hCE :
      c * Real.exp (-16 * b) ≤ (S.card : ℝ) * 2 := by
    calc
      c * Real.exp (-16 * b) ≤
          ((S.card : ℝ) * (2 / Real.exp (-16 * b))) *
            Real.exp (-16 * b) :=
        mul_le_mul_of_nonneg_right hCap hE.le
      _ = (S.card : ℝ) * 2 := by
        field_simp [ne_of_gt hE]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    (by nlinarith only [hCE])

/-- If actual retained links capture a positive fraction η of the
original Rayleigh, and the latter has floor c, then the true link
count must be at least η*c*exp(-16b)/2. This is conditional
and DOES NOT imply a volume-independent active-link fraction. -/
theorem p4Q2PZ37AAM_retained_fraction_of_Rayleigh_forces_linkCount
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (eta c : ℝ) (heta : 0 ≤ eta)
    (hFloor : c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)
    (hCapture :
      eta * p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb ≤
        p4Q2PZ37AAL_originalRetainedLinkRayleigh H b hb S) :
    (eta * c) * Real.exp (-16 * b) / 2 ≤ (S.card : ℝ) := by
  apply p4Q2PZ37AAM_retained_response_floor_forces_linkCount
    H b hb S (eta * c)
  exact (mul_le_mul_of_nonneg_left hFloor heta).trans hCapture

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAM_originalNormalizedLinkResponse_le_explicitPosteriorCap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAM_originalRetainedResponse_le_card_posteriorCap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAM_retained_response_floor_forces_linkCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAM_retained_fraction_of_Rayleigh_forces_linkCount
