import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalStaticPhysicalGLQuantitativeV5_PZ37ZP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalRawTaylorRemainderV5_PZ37ZQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullLinkGLPhysicalTriangleV5_PZ37ZR
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalCancellationLinearFineLowerV5_PZ37ZK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZS — genuine Wilson physical-source quadratic fine GL floor

Combine ZP's actual two-mode full-link GL Gram floor, ZQ's physical
raw-Wilson Taylor error, ZR's physical perturbation inequality, and
ZC's genuine all-physical-source upper GL bound, at fixed finite H
and positive frozen b. The fine transfer normalization scalar is
retained EXACTLY, without differentiation.

The genuine normalized Gauss-law physical cancellation is decomposed as
  F_t = S_t - s_t E_t,
  S_t = (1-s_t+s_t kappa_H t) U_H + (s_t t/2) W_H U_H,
  s_t = ||RawWilson_t||^-1.

All sources and pair-Haar posteriors remain the original physical ones.
No new axioms, sorry/admit/native_decide, compensating-context no-go
reversal, H-uniform/scale-uniform claim, endpoint E, H1-H4, or continuum
Yang-Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZS_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The actual inverse norm of the original UNNORMALIZED physical
one-slab Wilson operator. Never differentiate this scalar. -/
noncomputable def p4Q2PZ37ZS_originalRawInverseNorm
    (H : ℕ) (t : Set.Ici (0 : ℝ)) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property‖⁻¹

/-- Coefficients in the genuine physical (U_H,W_H U_H) source plane.
Only the genuine raw normalization s_t occurs. -/
noncomputable def p4Q2PZ37ZS_originalPhysicalStaticCoefficients
    (H : ℕ) (t : Set.Ici (0 : ℝ)) : Fin 2 → ℝ :=
  fun i =>
    if i = 0 then
      1 - p4Q2PZ37ZS_originalRawInverseNorm H t +
        p4Q2PZ37ZS_originalRawInverseNorm H t *
          p4Q2JE_originalWilsonHaarZeroDerivativeConstant H * (t : ℝ)
    else
      p4Q2PZ37ZS_originalRawInverseNorm H t * (t : ℝ) / 2

/-- The static part is EXACTLY ZN's authentic physical Wilson source. -/
noncomputable def p4Q2PZ37ZS_originalPhysicalStaticPart
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
  p4Q2PZ37ZN_originalStaticPhysicalSource H
    (p4Q2PZ37ZS_originalPhysicalStaticCoefficients H t)

/-- The normalized physical fine cancellation decomposes EXACTLY in
the original Gauss-law Haar Hilbert as static 2-mode source minus the
true physical Taylor remainder times inverse raw norm. -/
theorem p4Q2PZ37ZS_originalPhysicalCancellation_eq_static_sub_error
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    p4Q2PZ37ZE_originalPhysicalCancellation H t =
      p4Q2PZ37ZS_originalPhysicalStaticPart H t -
        p4Q2PZ37ZS_originalRawInverseNorm H t •
          p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let kappa : ℝ := p4Q2JE_originalWilsonHaarZeroDerivativeConstant H
  let Raw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let s : ℝ := p4Q2PZ37ZS_originalRawInverseNorm H t
  let D : Phys := p4Q2PZ37ZQ_originalPhysicalRawDerivative H
  let E : Phys := p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t
  have hD : D = (-(1 / 2 : ℝ)) • W - kappa • U := rfl
  have hRaw : Raw U = U + (t : ℝ) • D + E := by
    change Raw U = U + (t : ℝ) • D +
      (Raw U - U - (t : ℝ) • D)
    abel
  have hModule :
      U - s • (Raw U) =
        ((1 - s + s * kappa * (t : ℝ)) • U +
          (s * (t : ℝ) / 2) • W) - s • E := by
    rw [hRaw, hD]
    module
  calc
    p4Q2PZ37ZE_originalPhysicalCancellation H t =
        U - s • (Raw U) := by
      simp only [p4Q2PZ37ZE_originalPhysicalCancellation,
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine_apply]
      rfl
    _ = ((1 - s + s * kappa * (t : ℝ)) • U +
          (s * (t : ℝ) / 2) • W) - s • E := hModule
    _ = p4Q2PZ37ZS_originalPhysicalStaticPart H t -
          p4Q2PZ37ZS_originalRawInverseNorm H t •
            p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t := by
      rfl

/-- The second genuine spatial-Wilson coefficient is bounded by the
sup norm on Fin 2; this is sufficient for the quantitative ZP floor. -/
theorem p4Q2PZ37ZS_originalStaticCoefficients_norm_sq_ge_WilsonComponent
    (H : ℕ) (t : Set.Ici (0 : ℝ)) :
    (p4Q2PZ37ZS_originalRawInverseNorm H t * (t : ℝ) / 2)^2 ≤
      ‖p4Q2PZ37ZS_originalPhysicalStaticCoefficients H t‖^2 := by
  let a := p4Q2PZ37ZS_originalPhysicalStaticCoefficients H t
  have hCoord : ‖a (1 : Fin 2)‖ ≤ ‖a‖ :=
    norm_le_pi_norm a (1 : Fin 2)
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hCoord 2
  simpa [a, p4Q2PZ37ZS_originalPhysicalStaticCoefficients,
    Real.norm_eq_abs, sq_abs] using hSq


/-- The genuine static two-mode GL mass controls the squared coefficient
of the spatial Wilson direction, without differentiating s_t. -/
theorem p4Q2PZ37ZS_originalStaticPart_GL_lower
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (t : Set.Ici (0 : ℝ)) :
    ∃ m : ℝ, 0 < m ∧
      m * (p4Q2PZ37ZS_originalRawInverseNorm H t * (t : ℝ))^2 / 4 ≤
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b hb.le (p4Q2PZ37ZS_originalPhysicalStaticPart H t)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  obtain ⟨m, hm, hFloor⟩ :=
    p4Q2PZ37ZP_originalStaticPhysicalGLMass_exists_quadraticFloor
      H b hb e e' left₀ right₀
  let a := p4Q2PZ37ZS_originalPhysicalStaticCoefficients H t
  have hCoord :
      (p4Q2PZ37ZS_originalRawInverseNorm H t * (t : ℝ) / 2)^2 ≤ ‖a‖^2 :=
    p4Q2PZ37ZS_originalStaticCoefficients_norm_sq_ge_WilsonComponent H t
  have hFloorA : m * ‖a‖^2 ≤
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le (p4Q2PZ37ZS_originalPhysicalStaticPart H t)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :=
    hFloor a
  refine ⟨m, hm, ?_⟩
  calc
    m * (p4Q2PZ37ZS_originalRawInverseNorm H t * (t : ℝ))^2 / 4 =
        m * (p4Q2PZ37ZS_originalRawInverseNorm H t * (t : ℝ) / 2)^2 := by ring
    _ ≤ m * ‖a‖^2 := mul_le_mul_of_nonneg_left hCoord hm.le
    _ ≤ _ := hFloorA

/-- The TRUE original full-link GL mass of s_t E_t is O(t^4).
The upper bound is ZC's previously proved genuine all-physical-Hilbert
posterior estimate, not a newly assumed operator norm. -/
theorem p4Q2PZ37ZS_originalScaledTaylorError_GL_le_quartic
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (t : Set.Ici (0 : ℝ))
    (hsmall : ‖(t : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H‖ ≤ 1) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le
      (p4Q2PZ37ZS_originalRawInverseNorm H t •
        p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
    p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b *
      (p4Q2PZ37ZS_originalRawInverseNorm H t)^2 *
      ((t : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^4 := by
  let B := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let C := p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b
  let s := p4Q2PZ37ZS_originalRawInverseNorm H t
  let E := p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t
  let Mass :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 → ℝ :=
    fun f => p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hE : ‖E‖ ≤ ((t : ℝ) * B)^2 :=
    p4Q2PZ37ZQ_originalPhysicalRawTaylorError_norm_le_quadratic H t hsmall
  have hESq : ‖E‖^2 ≤ (((t : ℝ) * B)^2)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hE 2
  have hNorm : ‖s • E‖^2 = s^2 * ‖E‖^2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hC : 0 ≤ C := by
    dsimp [C, p4Q2PZ37ZG_originalFullLinkGL_RayleighCap]
    positivity
  have hOriginal : Mass (s • E) ≤ C * ‖s • E‖^2 := by
    have hZC :=
      p4Q2PZ37ZC_originalGL_fullLink_le_explicit_physicalSourceNorm
        H b hb (s • E)
    calc
      Mass (s • E) ≤
          ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
            (2 * ‖s • E‖^2)) / Real.exp (-16 * b) := hZC
      _ = C * ‖s • E‖^2 := by
        dsimp [C, p4Q2PZ37ZG_originalFullLinkGL_RayleighCap]
        ring
  change Mass (s • E) ≤ C * s^2 * ((t : ℝ) * B)^4
  calc
    Mass (s • E) ≤ C * ‖s • E‖^2 := hOriginal
    _ = C * (s^2 * ‖E‖^2) := by rw [hNorm]
    _ ≤ C * (s^2 * (((t : ℝ) * B)^2)^2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hESq (sq_nonneg s)) hC
    _ = C * s^2 * ((t : ℝ) * B)^4 := by ring

/-- Genuine ZP/ZQ/ZR/ZC exact combination:
  M_GL(F_t) >= s_t^2 t^2 (m/8 - C_GL B_H^4 t^2).
This is at fixed H,b, on the ACTUAL Wilson Taylor budget window,
with no positive small-fine interval chosen yet. -/
theorem p4Q2PZ37ZS_originalPhysicalGLMass_quadratic_minus_quartic
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (t : Set.Ici (0 : ℝ))
    (hsmall : ‖(t : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H‖ ≤ 1) :
    ∃ m : ℝ, 0 < m ∧
      (p4Q2PZ37ZS_originalRawInverseNorm H t)^2 * (t : ℝ)^2 *
        (m / 8 -
          p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^4 *
            (t : ℝ)^2) ≤
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le (p4Q2PZ37ZE_originalPhysicalCancellation H t)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let Phys := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let C : ℝ := p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b
  let s : ℝ := p4Q2PZ37ZS_originalRawInverseNorm H t
  let a : Fin 2 → ℝ := p4Q2PZ37ZS_originalPhysicalStaticCoefficients H t
  let S : Phys := p4Q2PZ37ZS_originalPhysicalStaticPart H t
  let E : Phys := p4Q2PZ37ZQ_originalPhysicalRawTaylorError H t
  let F : Phys := p4Q2PZ37ZE_originalPhysicalCancellation H t
  let Mass : Phys → ℝ := fun f =>
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  let psiS : C(Cfg, ℝ) :=
    a 0 • (1 : C(Cfg, ℝ)) + a 1 • p4Q2JI_actualSpatialWilsonContinuous H
  let psiE : C(Cfg, ℝ) :=
    p4Q2JF_originalWilsonHaarRowContinuous H (t : ℝ) -
      (1 : C(Cfg, ℝ)) -
      (t : ℝ) • p4Q2JE_originalWilsonHaarZeroDerivativeProfile H
  have hSRep : (S : Lp ℝ 2 haar) = L psiS :=
    p4Q2PZ37ZN_originalStaticPhysicalSource_coe_eq_toLp H a
  have hERep : ((s • E : Phys) : Lp ℝ 2 haar) = L (s • psiE) := by
    change s • (E : Lp ℝ 2 haar) = L (s • psiE)
    rw [p4Q2PZ37ZQ_originalPhysicalRawTaylorError_coe_eq_toLp H t, map_smul]
  obtain ⟨m, hm, hSFloor⟩ :=
    p4Q2PZ37ZS_originalStaticPart_GL_lower
      H b hb e e' left₀ right₀ t
  have hEUpper : Mass (s • E) ≤ C * s^2 * ((t : ℝ) * B)^4 :=
    p4Q2PZ37ZS_originalScaledTaylorError_GL_le_quartic H b hb t hsmall
  have hDecomp : F = S - s • E :=
    p4Q2PZ37ZS_originalPhysicalCancellation_eq_static_sub_error H t
  have hPerturb : Mass S / 2 - Mass (s • E) ≤ Mass F := by
    rw [hDecomp]
    exact p4Q2PZ37ZR_originalFullLinkGLMass_sub_lower
      H b hb S (s • E) psiS (s • psiE) hSRep hERep
  refine ⟨m, hm, ?_⟩
  change s^2 * (t : ℝ)^2 * (m / 8 - C * B^4 * (t : ℝ)^2) ≤ Mass F
  calc
    s^2 * (t : ℝ)^2 * (m / 8 - C * B^4 * (t : ℝ)^2) =
        (m * (s * (t : ℝ))^2 / 4) / 2 -
          C * s^2 * ((t : ℝ) * B)^4 := by ring
    _ ≤ Mass S / 2 - Mass (s • E) := by linarith
    _ ≤ Mass F := hPerturb

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalPhysicalCancellation_eq_static_sub_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalStaticCoefficients_norm_sq_ge_WilsonComponent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalStaticPart_GL_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalScaledTaylorError_GL_le_quartic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalPhysicalGLMass_quadratic_minus_quartic
