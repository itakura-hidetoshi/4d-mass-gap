import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSignedGlobalHaarCrossResidualV5_PZ37ABF
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABF2 — genuine single-plaquette physical GI response
# with the EXACT original transfer normalization explicitly retained

LW proves that the ORIGINAL interacting Wilson JH Gauss-law GI
continuous linear functional multiplied by the genuine one-slab
physical transfer norm t_(H,b)>0 has norm <= E_b, where E_b =
exp(8b)*(exp(16b)-exp(-16b)), independent of H, real link, and
original complete boundary pair. AAI proves the genuine ORIGINAL
single centered Wilson spatial plaquette Haar-L² norm is <=1.

ABD identified its physical source v_p exactly with half of the
Haar-centered local plaquette as tested by the original JH functional.
Thus, FOR EVERY true H,b>0,e,p,z:
    | t_(H,b) * Delta_physicalLocal,p(H,b,e,z) | <= E_b / 2.
This is an unconditional quantitative H-INDEPENDENT envelope
for the genuinely transfer-COMPENSATED local response.

The original UNCOMPENSATED local GI response has only
    |Delta_local| <= t_(H,b)^(-1)*E_b/2.
The physical transfer norm may vary with H; no uniform bound
for its reciprocal is assumed or claimed.

Further, the actual compensated local signed GI square is
integrable against the unchanged original full boundary pair-Haar:
    integral [t_(H,b)*Delta_local]^2 dμ_H <= (E_b/2)^2,
independent of H, link, plaquette, or original boundary context.
This supplies a real local L² ceiling without any artificial
posterior, local Gibbs cutoff or forged physical source.

It is an UPPER local GI response bound, NOT a common LOWER
signed full/local correlation or original unweighted GI gap moment,
and does not imply uniform physical mass gap or common fine
interval. No new axiom, sorry/admit/native_decide, JL legacy
native_decide, Dobrushin, Gray, E/F or H1-H4 closure.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABF2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABF2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABF2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABF2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABF2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- At every true physical boundary context, the ORIGINAL single
centered SU(2) Wilson plaquette Gauss-law GI detector has an actual
transfer-COMPENSATED H-INDEPENDENT envelope. The exact transfer
norm t is not set to one. -/
theorem p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGI_abs_le
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |p4Q2LW_originalPhysicalTransferNorm H b hb.le *
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z| ≤
      p4Q2LW_originalHarnackContrastScale b / 2 := by
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let Haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let V : Lp ℝ 2 Haar := p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p
  let J := p4Q2JH_originalGIResponseCLM H b hb.le e z
  let Q := p4Q2LW_originalTransferCompensatedGIResponse H b hb.le e z
  have hQ : ‖Q‖ ≤ E :=
    p4Q2LW_originalCompensatedGI_norm_le_HarnackContrast H b hb.le e z
  have hE : 0 ≤ E :=
    p4Q2LW_originalHarnackContrastScale_nonneg b hb.le
  have hV : ‖V‖ ≤ (1 : ℝ) :=
    p4Q2PZ37AAI_centeredPlaquette_norm_le_one H p
  have hJ : ‖Q V‖ ≤ E := by
    calc
      ‖Q V‖ ≤ ‖Q‖ * ‖V‖ := Q.le_opNorm V
      _ ≤ E * ‖V‖ :=
        mul_le_mul_of_nonneg_right hQ (norm_nonneg V)
      _ ≤ E * 1 := mul_le_mul_of_nonneg_left hV hE
      _ = E := mul_one _
  have hExact :
      t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z =
        (1 / 2 : ℝ) * Q V := by
    rw [← p4Q2PZ37ABD_localContribution_eq_originalPhysicalGIGap
      H b hb e z p]
    change t * ((1 / 2 : ℝ) * J V) =
      (1 / 2 : ℝ) * (t * J V)
    ring
  change |t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb.le
    (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z| ≤
    E / 2
  rw [hExact, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Real.norm_eq_abs] at hJ
  linarith

/-- No unproved normalization: the true UNCOMPENSATED local GI
amplitude has the exact physical transfer-norm inverse cost. -/
theorem p4Q2PZ37ABF2_originalPhysicalLocalGI_abs_le_transferInverse
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z| ≤
      (p4Q2LW_originalPhysicalTransferNorm H b hb.le)⁻¹ *
        (p4Q2LW_originalHarnackContrastScale b / 2) := by
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  have ht : 0 < t := p4Q2LW_originalPhysicalTransferNorm_pos H b hb.le
  have hComp :=
    p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGI_abs_le H b hb e p z
  change |t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb.le
    (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z| ≤
    E / 2 at hComp
  change |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb.le
    (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z| ≤
    t⁻¹ * (E / 2)
  rw [abs_mul, abs_of_pos ht] at hComp
  exact (le_inv_mul_iff₀ ht).mpr (by simpa [mul_comm] using hComp)

/-- Full original pair-Haar L² energy of the ACTUAL compensated
centered single-plaquette physical Wilson GI response. -/
noncomputable def p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ :=
  ∫ z,
    (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z)^2
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- True ORIGINAL complete-boundary pair-Haar L² mean of each
compensated local physical Wilson GI detector is bounded by the
SAME coupling-only E_b²/4, at ALL finite H and actual links/
plaquettes, with no assumption of spatial locality of Perron. -/
theorem p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment_le_uniform
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment
      H b hb e p ≤ (p4Q2LW_originalHarnackContrastScale b / 2)^2 := by
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let L : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z
  have hL : Continuous L :=
    p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e
  have hInt : Integrable (fun z : Pair => (t * L z)^2) μ :=
    ((continuous_const.mul hL).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hE : 0 ≤ E / 2 :=
    (p4Q2LW_originalHarnackContrastScale_nonneg b hb.le).trans_eq (by ring)
  have hPoint (z : Pair) : (t * L z)^2 ≤ (E / 2)^2 := by
    have hAbs :=
      p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGI_abs_le H b hb e p z
    change |t * L z| ≤ E / 2 at hAbs
    have hSq := pow_le_pow_left₀ (abs_nonneg _) hAbs 2
    simpa only [sq_abs] using hSq
  change (∫ z : Pair, (t * L z)^2 ∂μ) ≤ (E / 2)^2
  calc
    (∫ z : Pair, (t * L z)^2 ∂μ) ≤
        ∫ _z : Pair, (E / 2)^2 ∂μ := by
      apply integral_mono hInt (integrable_const _)
      exact hPoint
    _ = (E / 2)^2 := by simp

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGI_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABF2_originalPhysicalLocalGI_abs_le_transferInverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment_le_uniform
