import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalRawNormFirstVariationV5_PZ37ZV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZV2 — full original normalized Wilson fine tangent

The authentic SU(2) physical Wilson norm satisfies
|‖R_t‖ - (1+t d_H)| ≤ 9 (B_H t)², d_H=⟪D_H,U_H⟫.
The genuine normalized physical source is F_t=U_H-‖R_t‖⁻¹R_t U_H.

Define the norm difference quotient at nonzero positive fine and
extend it to fine=0 by d_H (NOT by the arbitrary value 0).
Prove its half-line continuity at zero. Then the exact identity
(1-s_t)/t = s_t (‖R_t‖-1)/t, s_t=‖R_t‖⁻¹,
identifies the longitudinal correction without differentiating s_t.

Combine PZ37ZT's true scalar-corrected Gauss-law strong tangent to get
the complete original normalized physical direction
  F_t/t -> (W_H - ⟪W_H,U_H⟫ U_H)/2
as t decreases to 0 through positive fine.

All statements use the ACTUAL physical transfer, source, Haar Hilbert
and original Wilson action, without any new axiom/sorry/admit/
native_decide, proxy posterior, volume/scale-uniform coercivity,
H1-H4 or continuum 4D Yang-Mills mass-gap assertion.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZV2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZV2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZV2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZV2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZV2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The EXACT raw physical Wilson top-norm difference quotient at
positive fine, continuously totalized at zero by its proven slope. -/
noncomputable def p4Q2PZ37ZV2_originalRawNormSlopeExtension
    (H : ℕ) (t : Set.Ici (0 : ℝ)) : ℝ :=
  if (t : ℝ) = 0 then
    inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
  else
    (t : ℝ)⁻¹ *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property‖ - 1)

/-- On genuinely positive fine, no extension changes the literal
difference quotient of the ORIGINAL raw Wilson operator norm. -/
theorem p4Q2PZ37ZV2_originalRawNormSlopeExtension_positive
    (H : ℕ) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ)) :
    p4Q2PZ37ZV2_originalRawNormSlopeExtension H t =
      (t : ℝ)⁻¹ *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property‖ - 1) := by
  unfold p4Q2PZ37ZV2_originalRawNormSlopeExtension
  rw [if_neg (ne_of_gt ht)]

/-- Uniform first-order error for the continuously extended genuine
raw-norm quotient, including fine zero. -/
theorem p4Q2PZ37ZV2_originalRawNormSlopeExtension_linearError
    (H : ℕ) (t : Set.Ici (0 : ℝ))
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (t : ℝ) ≤ (1 / 4 : ℝ)) :
    |p4Q2PZ37ZV2_originalRawNormSlopeExtension H t -
        inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)| ≤
      9 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2 *
        (t : ℝ) := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let D := p4Q2PZ37ZQ_originalPhysicalRawDerivative H
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let d : ℝ := inner ℝ D U
  by_cases ht0 : (t : ℝ) = 0
  · have htEq : t = (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)) :=
      Subtype.ext ht0
    rw [htEq]
    simp [p4Q2PZ37ZV2_originalRawNormSlopeExtension]
  · have ht : 0 < (t : ℝ) := lt_of_le_of_ne t.property (Ne.symm ht0)
    have h9 : |‖R‖ - (1 + (t : ℝ) * d)| ≤ 9 * (B * (t : ℝ))^2 :=
      p4Q2PZ37ZV_originalPhysicalRawNorm_firstOrder_error H t hsmall
    change |p4Q2PZ37ZV2_originalRawNormSlopeExtension H t - d| ≤
      9 * B^2 * (t : ℝ)
    rw [p4Q2PZ37ZV2_originalRawNormSlopeExtension_positive H t ht]
    have hIdentity :
        (t : ℝ)⁻¹ * (‖R‖ - 1) - d =
          (t : ℝ)⁻¹ * (‖R‖ - (1 + (t : ℝ) * d)) := by
      field_simp [ht0]
    rw [hIdentity, abs_mul, abs_inv, abs_of_pos ht]
    calc
      (t : ℝ)⁻¹ * |‖R‖ - (1 + (t : ℝ) * d)| ≤
          (t : ℝ)⁻¹ * (9 * (B * (t : ℝ))^2) :=
        mul_le_mul_of_nonneg_left h9 (inv_nonneg.mpr ht.le)
      _ = 9 * B^2 * (t : ℝ) := by
        field_simp [ht0]
        ring

/-- Genuine Wilson raw physical top-norm first-order quotient tends
to its authentic physical vacuum coefficient from positive fine;
continuity is established for the slope-filled extension. -/
theorem p4Q2PZ37ZV2_originalRawNormSlopeExtension_tendsto
    (H : ℕ) :
    Tendsto (p4Q2PZ37ZV2_originalRawNormSlopeExtension H)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))) := by
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let d : ℝ := inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
  let δ : ℝ := 1 / (4 * (B + 1))
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hDen : 0 < 4 * (B + 1) := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hNear : ∀ᶠ t : Set.Ici (0 : ℝ) in 𝓝 t0, (t : ℝ) < δ := by
    have hOpen : IsOpen {t : Set.Ici (0 : ℝ) | (t : ℝ) < δ} :=
      isOpen_lt continuous_subtype_val continuous_const
    exact hOpen.mem_nhds (by change (0 : ℝ) < δ; exact hδ)
  have hError (t : Set.Ici (0 : ℝ)) (htδ : (t : ℝ) < δ) :
      |p4Q2PZ37ZV2_originalRawNormSlopeExtension H t - d| ≤
        9 * B^2 * (t : ℝ) := by
    have hProd : (t : ℝ) * (4 * (B + 1)) < 1 :=
      (lt_div_iff₀ hDen).mp htδ
    have hBudget : B * (t : ℝ) ≤ (1 / 4 : ℝ) := by
      nlinarith [t.property]
    exact p4Q2PZ37ZV2_originalRawNormSlopeExtension_linearError
      H t hBudget
  have hVal :
      Tendsto (fun t : Set.Ici (0 : ℝ) => (t : ℝ))
        (𝓝 t0) (𝓝 (0 : ℝ)) := by
    exact continuous_subtype_val.continuousAt
  have hUpper :
      Tendsto (fun t : Set.Ici (0 : ℝ) => 9 * B^2 * (t : ℝ))
        (𝓝 t0) (𝓝 (0 : ℝ)) := by
    simpa using hVal.const_mul (9 * B^2)
  have hAbs :
      Tendsto (fun t : Set.Ici (0 : ℝ) =>
        |p4Q2PZ37ZV2_originalRawNormSlopeExtension H t - d|)
        (𝓝 t0) (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hUpper
      (Filter.Eventually.of_forall
        (fun t => abs_nonneg (p4Q2PZ37ZV2_originalRawNormSlopeExtension H t - d)))
      (hNear.mono (fun t ht => hError t ht))
  change Tendsto (p4Q2PZ37ZV2_originalRawNormSlopeExtension H)
    (𝓝 t0) (𝓝 d)
  rw [Metric.tendsto_nhds] at hAbs ⊢
  intro eps heps
  filter_upwards [hAbs eps heps] with t ht
  simpa [Real.dist_eq, abs_abs] using ht

/-- The original exact long-axis contribution after dividing by fine
is reconstructed with the norm quotient, avoiding a normalization
derivative. At fine zero it is filled by the unique true limit. -/
noncomputable def p4Q2PZ37ZV2_originalLongitudinalSlopeExtension
    (H : ℕ) (t : Set.Ici (0 : ℝ)) : ℝ :=
  p4Q2PZ37ZS_originalRawInverseNorm H t *
    (p4Q2PZ37ZV2_originalRawNormSlopeExtension H t +
      p4Q2JE_originalWilsonHaarZeroDerivativeConstant H)

/-- Exact equality of the longitudinal slope of the authentic physical
normalized cancellation with its norm-slope extension at positive fine. -/
theorem p4Q2PZ37ZV2_originalLongitudinalSlopeExtension_positive
    (H : ℕ) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ)) :
    (t : ℝ)⁻¹ * p4Q2PZ37ZT_originalLongitudinalCoefficient H t =
      p4Q2PZ37ZV2_originalLongitudinalSlopeExtension H t := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let k : ℝ := p4Q2JE_originalWilsonHaarZeroDerivativeConstant H
  have hR : 0 < ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  change (t : ℝ)⁻¹ *
    (1 - ‖R‖⁻¹ + ‖R‖⁻¹ * k * (t : ℝ)) =
      ‖R‖⁻¹ * (p4Q2PZ37ZV2_originalRawNormSlopeExtension H t + k)
  rw [p4Q2PZ37ZV2_originalRawNormSlopeExtension_positive H t ht]
  field_simp [ne_of_gt ht, ne_of_gt hR]
  ring

/-- Longitudinal normalized Wilson fine slope equals the negative
one-half of the ORIGINAL centered spatial Wilson Haar mean. -/
theorem p4Q2PZ37ZV2_originalLongitudinalSlopeExtension_tendsto
    (H : ℕ) :
    Tendsto (p4Q2PZ37ZV2_originalLongitudinalSlopeExtension H)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (-(1 / 2 : ℝ) * inner ℝ
        (p4Q2JU_originalSpatialWilsonPhysicalSource H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))) := by
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  let s := p4Q2PZ37ZS_originalRawInverseNorm H
  let q := p4Q2PZ37ZV2_originalRawNormSlopeExtension H
  let k : ℝ := p4Q2JE_originalWilsonHaarZeroDerivativeConstant H
  let d : ℝ := inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
  let w : ℝ := inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
  have hs : Tendsto s (𝓝 t0) (𝓝 (1 : ℝ)) :=
    p4Q2PZ37ZT_originalRawInverseNorm_tendsto_one H
  have hq : Tendsto q (𝓝 t0) (𝓝 d) :=
    p4Q2PZ37ZV2_originalRawNormSlopeExtension_tendsto H
  have hCoeff : d + k = -(1 / 2 : ℝ) * w := by
    change inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) +
      p4Q2JE_originalWilsonHaarZeroDerivativeConstant H =
      -(1 / 2 : ℝ) * inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
    rw [p4Q2PZ37ZV_originalPhysicalRawDerivative_vacuum_coeff H]
    ring
  have hProd : Tendsto (fun t : Set.Ici (0 : ℝ) => s t * (q t + k))
      (𝓝 t0) (𝓝 (d + k)) := by
    simpa using hs.mul (hq.add_const k)
  change Tendsto (fun t : Set.Ici (0 : ℝ) => s t * (q t + k))
    (𝓝 t0) (𝓝 (-(1 / 2 : ℝ) * w))
  rw [← hCoeff]
  exact hProd

/-- The actual normalized physical source divided by fine, filled at
t=0 by the unique strong limit through the exact longitudinal and
scalar-corrected coordinates. -/
noncomputable def p4Q2PZ37ZV2_originalFullPhysicalTangentExtension
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  p4Q2PZ37ZV2_originalLongitudinalSlopeExtension H t •
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 +
  p4Q2PZ37ZT_originalScalarCorrectedTangent H t

/-- The filled physical tangent is exactly F_t/t on every positive
genuine fine coupling, in the UNCHANGED Gauss-law physical Hilbert. -/
theorem p4Q2PZ37ZV2_originalFullPhysicalTangentExtension_positive
    (H : ℕ) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ)) :
    (t : ℝ)⁻¹ • p4Q2PZ37ZE_originalPhysicalCancellation H t =
      p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H t := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let F : Phys := p4Q2PZ37ZE_originalPhysicalCancellation H t
  let A : ℝ := p4Q2PZ37ZT_originalLongitudinalCoefficient H t
  let Q : Phys := p4Q2PZ37ZT_originalScalarCorrectedTangent H t
  have hLong :=
    p4Q2PZ37ZV2_originalLongitudinalSlopeExtension_positive H t ht
  have hQ :=
    p4Q2PZ37ZT_originalScalarCorrectedTangent_eq_truePhysical H t ht
  change (t : ℝ)⁻¹ • F =
    p4Q2PZ37ZV2_originalLongitudinalSlopeExtension H t • U +
      p4Q2PZ37ZT_originalScalarCorrectedTangent H t
  rw [← hLong, hQ]
  rw [smul_sub, smul_smul]
  module

/-- True strong Wilson physical tangent at fine zero. The longitudinal
spectral normalization term exactly centers the genuine Wilson action.
There is no differentiation of the original top operator norm. -/
theorem p4Q2PZ37ZV2_originalFullPhysicalTangentExtension_tendsto
    (H : ℕ) :
    Tendsto (p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 ((1 / 2 : ℝ) •
        (p4Q2JU_originalSpatialWilsonPhysicalSource H -
          (inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) •
            periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))) := by
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let w : ℝ := inner ℝ W U
  let a := p4Q2PZ37ZV2_originalLongitudinalSlopeExtension H
  let Q := p4Q2PZ37ZT_originalScalarCorrectedTangent H
  have ha : Tendsto a (𝓝 t0) (𝓝 (-(1 / 2 : ℝ) * w)) :=
    p4Q2PZ37ZV2_originalLongitudinalSlopeExtension_tendsto H
  have hQ : Tendsto Q (𝓝 t0) (𝓝 ((1 / 2 : ℝ) • W)) :=
    p4Q2PZ37ZT_originalScalarCorrectedTangent_tendsto H
  have hU : Tendsto (fun t : Set.Ici (0 : ℝ) => a t • U)
      (𝓝 t0) (𝓝 ((-(1 / 2 : ℝ) * w) • U)) := by
    simpa using ha.smul (tendsto_const_nhds :
      Tendsto (fun _ : Set.Ici (0 : ℝ) => U) (𝓝 t0) (𝓝 U))
  have hSum : Tendsto (fun t : Set.Ici (0 : ℝ) => a t • U + Q t)
      (𝓝 t0) (𝓝 ((-(1 / 2 : ℝ) * w) • U + (1 / 2 : ℝ) • W)) :=
    hU.add hQ
  have hTarget :
      (-(1 / 2 : ℝ) * w) • U + (1 / 2 : ℝ) • W =
        (1 / 2 : ℝ) • (W - w • U) := by
    module
  change Tendsto (fun t : Set.Ici (0 : ℝ) => a t • U + Q t)
    (𝓝 t0) (𝓝 ((1 / 2 : ℝ) • (W - w • U)))
  rw [← hTarget]
  exact hSum

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV2_originalRawNormSlopeExtension_positive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV2_originalRawNormSlopeExtension_linearError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV2_originalRawNormSlopeExtension_tendsto
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV2_originalLongitudinalSlopeExtension_positive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV2_originalLongitudinalSlopeExtension_tendsto
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV2_originalFullPhysicalTangentExtension_positive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZV2_originalFullPhysicalTangentExtension_tendsto
