import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalGLQuadraticFineFloorV5_PZ37ZS
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZT — true Wilson Gauss-law transverse fine tangent

The original physical cancellation is F_t = U - ||Raw_t||⁻¹ Raw_t U.
PZ37ZS proved F_t = A_t U + (s_t t / 2) W - s_t E_t, where
A_t = 1 - s_t + s_t kappa_H t and ||E_t|| <= (t B_H)^2.

This module proves, at every original finite H, that s_t tends to 1,
that t⁻¹ E_t tends to 0 in the authentic physical Hilbert, and thus that

  t⁻¹ (F_t - A_t U) -> (1/2) W_H U.

The scalar A_t, NOT an invented centered-source normalization, is
removed explicitly. This is the exact scalar-corrected physical tangent,
not the full physical tangent: its unknown longitudinal slope is isolated.

It does not differentiate the raw Wilson operator norm or conclude
that the original physical GL Rayleigh has a fine-zero limit.
No substitute posterior, new axioms/sorry/admit/native_decide,
volume/scale uniformity, endpoint E, H1-H4 or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Continuity of the EXACT inverse raw-physical Wilson operator norm
on its original nonnegative fine coupling half-line. -/
theorem p4Q2PZ37ZT_originalRawInverseNorm_continuous (H : ℕ) :
    Continuous (p4Q2PZ37ZS_originalRawInverseNorm H) := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine
      H 2 specialUnitaryTwoWilsonRankPositive
  have hC : Continuous (fun t : Set.Ici (0 : ℝ) => ‖R t‖) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_norm_continuous
      H 2 specialUnitaryTwoWilsonRankPositive
  have hne : ∀ t : Set.Ici (0 : ℝ), ‖R t‖ ≠ 0 := by
    intro t
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperatorHalfLine_norm_ne_zero
      H 2 specialUnitaryTwoWilsonRankPositive t
  change Continuous (fun t : Set.Ici (0 : ℝ) => ‖R t‖⁻¹)
  exact hC.inv₀ hne

/-- At genuine zero fine, raw Wilson is the rank-one Haar projection
of operator norm 1, hence the exact normalization inverse equals 1. -/
theorem p4Q2PZ37ZT_originalRawInverseNorm_zero (H : ℕ) :
    p4Q2PZ37ZS_originalRawInverseNorm H
      (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)) = 1 := by
  unfold p4Q2PZ37ZS_originalRawInverseNorm
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm]
  exact inv_one

/-- The original inverse normalization tends to 1 as positive fine
approaches zero. Only continuity is used, not differentiability. -/
theorem p4Q2PZ37ZT_originalRawInverseNorm_tendsto_one (H : ℕ) :
    Tendsto (p4Q2PZ37ZS_originalRawInverseNorm H)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ))) (𝓝 (1 : ℝ)) := by
  have h := (p4Q2PZ37ZT_originalRawInverseNorm_continuous H).continuousAt
    (x := (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
  rw [p4Q2PZ37ZT_originalRawInverseNorm_zero] at h
  exact h

/-- The TRUE physical raw Wilson Taylor error divided by fine,
totalized at fine=0 by the usual real inverse. -/
noncomputable def p4Q2PZ37ZT_originalPhysicalErrorDivFine
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  (t : ℝ)⁻¹ • p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t

/-- This totalized physical error quotient vanishes at fine=0. -/
theorem p4Q2PZ37ZT_originalPhysicalErrorDivFine_zero (H : ℕ) :
    p4Q2PZ37ZT_originalPhysicalErrorDivFine H
      (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)) = 0 := by
  simp [p4Q2PZ37ZT_originalPhysicalErrorDivFine]

/-- ZQ's genuine quadratic physical Taylor remainder becomes an
O_H(t) physical-Hilbert error after dividing by nonzero fine. -/
theorem p4Q2PZ37ZT_originalPhysicalErrorDivFine_norm_le_linear
    (H : ℕ) (t : Set.Ici (0 : ℝ))
    (ht : 0 < (t : ℝ))
    (hsmall : ‖(t : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H‖ ≤ 1) :
    ‖p4Q2PZ37ZT_originalPhysicalErrorDivFine H t‖ ≤
      (t : ℝ) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2 := by
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let E := p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t
  have hE : ‖E‖ ≤ ((t : ℝ) * B)^2 :=
    p4Q2PZ37ZQ_originalPhysicalRawTaylorError_norm_le_quadratic H t hsmall
  change ‖(t : ℝ)⁻¹ • E‖ ≤ (t : ℝ) * B^2
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
  calc
    (t : ℝ)⁻¹ * ‖E‖ ≤ (t : ℝ)⁻¹ * (((t : ℝ) * B)^2) :=
      mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr ht.le)
    _ = (t : ℝ) * B^2 := by
      field_simp [ne_of_gt ht]
      ring

/-- At any genuine finite H, the actual physical first-order
Taylor-error quotient tends STRONGLY to zero in the true Gauss-law
Haar Hilbert, along the half-line approaching fine=0. -/
theorem p4Q2PZ37ZT_originalPhysicalErrorDivFine_tendsto_zero
    (H : ℕ) :
    Tendsto (p4Q2PZ37ZT_originalPhysicalErrorDivFine H)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (0 :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)) := by
  let t0 : Set.Ici (0 : ℝ) := ⟨0, le_refl (0 : ℝ)⟩
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let delta : ℝ := 1 / (B + 1)
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hB1 : 0 < B + 1 := by linarith
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hNear : ∀ᶠ t : Set.Ici (0 : ℝ) in 𝓝 t0, (t : ℝ) < delta := by
    have hOpen : IsOpen {t : Set.Ici (0 : ℝ) | (t : ℝ) < delta} :=
      isOpen_lt continuous_subtype_val continuous_const
    exact hOpen.mem_nhds (by change (0 : ℝ) < delta; exact hdelta)
  have hBound (t : Set.Ici (0 : ℝ)) (ht : (t : ℝ) < delta) :
      ‖p4Q2PZ37ZT_originalPhysicalErrorDivFine H t‖ ≤ (t : ℝ) * B^2 := by
    have hProduct : (t : ℝ) * (B + 1) < 1 :=
      (lt_div_iff₀ hB1).mp ht
    have htBudget : (t : ℝ) * B ≤ 1 := by
      nlinarith [t.property]
    have hsmall : ‖(t : ℝ) * B‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg t.property hB)]
      exact htBudget
    rcases lt_or_eq_of_le t.property with htPos | htZero
    · exact p4Q2PZ37ZT_originalPhysicalErrorDivFine_norm_le_linear H t htPos hsmall
    · have hz : (t : ℝ) = 0 := htZero.symm
      simp [p4Q2PZ37ZT_originalPhysicalErrorDivFine, hz]
  have hVal :
      Tendsto (fun t : Set.Ici (0 : ℝ) => (t : ℝ)) (𝓝 t0) (𝓝 (0 : ℝ)) := by
    exact continuous_subtype_val.continuousAt
  have hUpper :
      Tendsto (fun t : Set.Ici (0 : ℝ) => (t : ℝ) * B^2)
        (𝓝 t0) (𝓝 (0 : ℝ)) := by
    simpa using hVal.mul_const (B^2)
  have hNorm :
      Tendsto (fun t : Set.Ici (0 : ℝ) =>
        ‖p4Q2PZ37ZT_originalPhysicalErrorDivFine H t‖)
        (𝓝 t0) (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hUpper
      (Filter.Eventually.of_forall
        (fun t => norm_nonneg (p4Q2PZ37ZT_originalPhysicalErrorDivFine H t)))
      (hNear.mono (fun t ht => hBound t ht))
  rw [Metric.tendsto_nhds] at hNorm ⊢
  intro eps heps
  filter_upwards [hNorm eps heps] with t ht
  simpa [Real.dist_eq, dist_zero, abs_of_nonneg
    (norm_nonneg (p4Q2PZ37ZT_originalPhysicalErrorDivFine H t))] using ht

/-- The actual unknown longitudinal coefficient in the physical
source's first-order decomposition, kept exact and undifferentiated. -/
noncomputable def p4Q2PZ37ZT_originalLongitudinalCoefficient
    (H : ℕ) (t : Set.Ici (0 : ℝ)) : ℝ :=
  1 - p4Q2PZ37ZS_originalRawInverseNorm H t +
    p4Q2PZ37ZS_originalRawInverseNorm H t *
      p4Q2JE_originalWilsonHaarZeroDerivativeConstant H * (t : ℝ)

/-- The authentic scalar-corrected physical fine tangent. The formula
contains only s_t, W_H, and the genuine raw physical error divided by
fine; it is total even at fine=0. -/
noncomputable def p4Q2PZ37ZT_originalScalarCorrectedTangent
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  let s := p4Q2PZ37ZS_originalRawInverseNorm H t
  (s / 2) • p4Q2JU_originalSpatialWilsonPhysicalSource H -
    s • p4Q2PZ37ZT_originalPhysicalErrorDivFine H t

/-- Exact positive-fine identity: subtract the original scalar
longitudinal part from the true normalized physical cancellation and
divide by t. No derivative of s_t is taken. -/
theorem p4Q2PZ37ZT_originalScalarCorrectedTangent_eq_truePhysical
    (H : ℕ) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ)) :
    p4Q2PZ37ZT_originalScalarCorrectedTangent H t =
      (t : ℝ)⁻¹ •
        (p4Q2PZ37ZE_originalPhysicalCancellation H t -
          p4Q2PZ37ZT_originalLongitudinalCoefficient H t •
            periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let s : ℝ := p4Q2PZ37ZS_originalRawInverseNorm H t
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let E : Phys := p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t
  let A : ℝ := p4Q2PZ37ZT_originalLongitudinalCoefficient H t
  have hSplit :
      p4Q2PZ37ZE_originalPhysicalCancellation H t - A • U =
        (s * (t : ℝ) / 2) • W - s • E := by
    rw [p4Q2PZ37ZS_originalPhysicalCancellation_eq_static_sub_error]
    change ((A • U + (s * (t : ℝ) / 2) • W) - s • E) - A • U =
      (s * (t : ℝ) / 2) • W - s • E
    module
  have hScalar : (t : ℝ)⁻¹ * (s * (t : ℝ) / 2) = s / 2 := by
    field_simp [ne_of_gt ht]
    ring
  change (s / 2) • W - s • ((t : ℝ)⁻¹ • E) =
    (t : ℝ)⁻¹ •
      (p4Q2PZ37ZE_originalPhysicalCancellation H t - A • U)
  rw [hSplit, smul_sub, smul_smul, smul_smul, hScalar]
  rw [mul_comm (t : ℝ)⁻¹ s]

/-- The exact scalar-corrected first-order physical Wilson direction
has the unconditional STRONG Haar-Hilbert limit W_H/2 at fine=0.
This is not yet the uncorrected physical tangent nor the GL ratio
limit: those additionally require the longitudinal normalization slope. -/
theorem p4Q2PZ37ZT_originalScalarCorrectedTangent_tendsto
    (H : ℕ) :
    Tendsto (p4Q2PZ37ZT_originalScalarCorrectedTangent H)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 ((1 / 2 : ℝ) • p4Q2JU_originalSpatialWilsonPhysicalSource H)) := by
  let s := p4Q2PZ37ZS_originalRawInverseNorm H
  let W := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let E := p4Q2PZ37ZT_originalPhysicalErrorDivFine H
  have hs : Tendsto s
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ))) (𝓝 (1 : ℝ)) :=
    p4Q2PZ37ZT_originalRawInverseNorm_tendsto_one H
  have hE : Tendsto E
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (0 :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)) :=
    p4Q2PZ37ZT_originalPhysicalErrorDivFine_tendsto_zero H
  have hW : Tendsto (fun t : Set.Ici (0 : ℝ) => (s t / 2) • W)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 ((1 / 2 : ℝ) • W)) := by
    simpa using (hs.div_const 2).smul (tendsto_const_nhds : Tendsto
      (fun _ : Set.Ici (0 : ℝ) => W)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ))) (𝓝 W))
  have hProd : Tendsto (fun t : Set.Ici (0 : ℝ) => s t • E t)
      (𝓝 (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
      (𝓝 (0 :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)) := by
    simpa using hs.smul hE
  change Tendsto (fun t : Set.Ici (0 : ℝ) =>
    (s t / 2) • W - s t • E t) _ _
  simpa using hW.sub hProd

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZT_originalRawInverseNorm_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZT_originalRawInverseNorm_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZT_originalRawInverseNorm_tendsto_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZT_originalPhysicalErrorDivFine_norm_le_linear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZT_originalPhysicalErrorDivFine_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZT_originalScalarCorrectedTangent_eq_truePhysical
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZT_originalScalarCorrectedTangent_tendsto
