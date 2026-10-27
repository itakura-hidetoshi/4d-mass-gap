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
  have hSq : ‖a (1 : Fin 2)‖^2 ≤ ‖a‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hCoord 2
  have hElem : a (1 : Fin 2) =
      p4Q2PZ37ZS_originalRawInverseNorm H t * (t : ℝ) / 2 := by
    dsimp [a, p4Q2PZ37ZS_originalPhysicalStaticCoefficients]
  rw [hElem, Real.norm_eq_abs] at hSq
  simpa only [sq_abs] using hSq


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
theorem p4Q2PZ37ZS_originalPhysicalGLMass_quadratic_minus_quartic_of_fixed_floor
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (m : ℝ) (hm : 0 < m)
    (hFloor : ∀ a : Fin 2 → ℝ,
      m * ‖a‖^2 ≤
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
    (t : Set.Ici (0 : ℝ))
    (hsmall : ‖(t : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H‖ ≤ 1) :
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
  have hCoord :
      (s * (t : ℝ) / 2)^2 ≤ ‖a‖^2 :=
    p4Q2PZ37ZS_originalStaticCoefficients_norm_sq_ge_WilsonComponent H t
  have hFloorA : m * ‖a‖^2 ≤ Mass S := hFloor a
  have hSFloor : m * (s * (t : ℝ))^2 / 4 ≤ Mass S := by
    calc
      m * (s * (t : ℝ))^2 / 4 = m * (s * (t : ℝ) / 2)^2 := by ring
      _ ≤ m * ‖a‖^2 := mul_le_mul_of_nonneg_left hCoord hm.le
      _ ≤ Mass S := hFloorA
  have hEUpper : Mass (s • E) ≤ C * s^2 * ((t : ℝ) * B)^4 :=
    p4Q2PZ37ZS_originalScaledTaylorError_GL_le_quartic H b hb t hsmall
  have hDecomp : F = S - s • E :=
    p4Q2PZ37ZS_originalPhysicalCancellation_eq_static_sub_error H t
  have hPerturb : Mass S / 2 - Mass (s • E) ≤ Mass F := by
    rw [hDecomp]
    exact p4Q2PZ37ZR_originalFullLinkGLMass_sub_lower
      H b hb S (s • E) psiS (s • psiE) hSRep hERep
  change s^2 * (t : ℝ)^2 * (m / 8 - C * B^4 * (t : ℝ)^2) ≤ Mass F
  calc
    s^2 * (t : ℝ)^2 * (m / 8 - C * B^4 * (t : ℝ)^2) =
        (m * (s * (t : ℝ))^2 / 4) / 2 -
          C * s^2 * ((t : ℝ) * B)^4 := by ring
    _ ≤ Mass S / 2 - Mass (s • E) := by linarith
    _ ≤ Mass F := hPerturb

/-- Existential form for an arbitrary actual frozen finite Wilson
model. Its witness m is chosen ONCE from ZP, independently of fine t. -/
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
  obtain ⟨m, hm, hFloor⟩ :=
    p4Q2PZ37ZP_originalStaticPhysicalGLMass_exists_quadraticFloor
      H b hb e e' left₀ right₀
  exact ⟨m, hm,
    p4Q2PZ37ZS_originalPhysicalGLMass_quadratic_minus_quartic_of_fixed_floor
      H b hb m hm hFloor t hsmall⟩


/-- The literal normalization inverse is bounded below on 0 ≤ t ≤ 1
by the original finite-volume Wilson action budget. This is an
algebraic reciprocal bound, not a derivative of the normalization. -/
theorem p4Q2PZ37ZS_originalRawInverseNorm_ge_budgetReciprocal
    (H : ℕ) (t : Set.Ici (0 : ℝ)) (ht : (t : ℝ) ≤ 1) :
    1 / (1 + periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) ≤
      p4Q2PZ37ZS_originalRawInverseNorm H t := by
  let Raw := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let B := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hRawPos : 0 < ‖Raw‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  have hCap : ‖Raw‖ ≤ 1 + B :=
    p4Q2PZ37ZK_originalRawOperator_norm_le_one_add_budget H t ht
  have hInv : 1 / (1 + B) ≤ 1 / ‖Raw‖ :=
    one_div_le_one_div_of_le hRawPos hCap
  simpa only [one_div, p4Q2PZ37ZS_originalRawInverseNorm] using hInv

/-- A FINITE-H frozen-b positive fine interval on which the authentic
original Wilson physical GL mass has a strictly positive quadratic
lower bound d_(H,b) t^2. The SAME m from ZP is used for ALL t on
this interval, and the raw inverse norm is not differentiated. -/
theorem p4Q2PZ37ZS_originalPhysicalGLMass_exists_uniform_quadraticFine
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ delta d : ℝ, 0 < delta ∧ 0 < d ∧
      ∀ t : Set.Ici (0 : ℝ),
        0 < (t : ℝ) → (t : ℝ) < delta →
        d * (t : ℝ)^2 ≤
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            H b hb.le (p4Q2PZ37ZE_originalPhysicalCancellation H t)
            (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let C : ℝ := p4Q2PZ37ZG_originalFullLinkGL_RayleighCap H b
  let Mass (t : Set.Ici (0 : ℝ)) : ℝ :=
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass H b hb.le
      (p4Q2PZ37ZE_originalPhysicalCancellation H t)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hC : 0 ≤ C := by
    dsimp [C, p4Q2PZ37ZG_originalFullLinkGL_RayleighCap]
    positivity
  obtain ⟨m, hm, hFloor⟩ :=
    p4Q2PZ37ZP_originalStaticPhysicalGLMass_exists_quadraticFloor
      H b hb e e' left₀ right₀
  let K : ℝ := C * B^4
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB1 : 0 < B + 1 := by linarith
  have hK1 : 0 < K + 1 := by linarith
  let delta : ℝ := min 1 (min (1 / (B + 1)) (m / (16 * (K + 1))))
  let d : ℝ := (1 / (1 + B))^2 * (m / 16)
  have hdelta : 0 < delta := by
    dsimp [delta]
    apply lt_min (by norm_num)
    exact lt_min (by positivity) (by positivity)
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨delta, d, hdelta, hd, ?_⟩
  intro t ht htdelta
  let s : ℝ := p4Q2PZ37ZS_originalRawInverseNorm H t
  have htOne : (t : ℝ) < 1 :=
    lt_of_lt_of_le htdelta (min_le_left _ _)
  have htBWindow : (t : ℝ) < 1 / (B + 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le htdelta (min_le_right _ _))
      (min_le_left _ _)
  have htKWindow : (t : ℝ) < m / (16 * (K + 1)) :=
    lt_of_lt_of_le (lt_of_lt_of_le htdelta (min_le_right _ _))
      (min_le_right _ _)
  have htBudget : (t : ℝ) * B ≤ 1 := by
    have hProd : (t : ℝ) * (B + 1) < 1 :=
      (lt_div_iff₀ hB1).mp htBWindow
    nlinarith
  have hsmall : ‖(t : ℝ) * B‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.le hB)]
    exact htBudget
  have hCut : K * (t : ℝ)^2 ≤ m / 16 := by
    have hProd : (t : ℝ) * (16 * (K + 1)) < m :=
      (lt_div_iff₀ (by positivity : 0 < 16 * (K + 1))).mp htKWindow
    have hTsq : (t : ℝ)^2 ≤ (t : ℝ) := by
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htOne.le)]
    have hMonotone : K * (t : ℝ)^2 ≤ K * (t : ℝ) :=
      mul_le_mul_of_nonneg_left hTsq hK
    nlinarith
  have hExact :
      s^2 * (t : ℝ)^2 * (m / 8 - K * (t : ℝ)^2) ≤ Mass t := by
    exact p4Q2PZ37ZS_originalPhysicalGLMass_quadratic_minus_quartic_of_fixed_floor
      H b hb m hm hFloor t hsmall
  have hBracket : m / 16 ≤ m / 8 - K * (t : ℝ)^2 := by linarith
  have hSlope :
      s^2 * (t : ℝ)^2 * (m / 16) ≤
      s^2 * (t : ℝ)^2 * (m / 8 - K * (t : ℝ)^2) :=
    mul_le_mul_of_nonneg_left hBracket
      (mul_nonneg (sq_nonneg s) (sq_nonneg (t : ℝ)))
  have hsLower : 1 / (1 + B) ≤ s :=
    p4Q2PZ37ZS_originalRawInverseNorm_ge_budgetReciprocal H t htOne.le
  have hsSq : (1 / (1 + B))^2 ≤ s^2 :=
    pow_le_pow_left₀ (by positivity) hsLower 2
  change d * (t : ℝ)^2 ≤ Mass t
  calc
    d * (t : ℝ)^2 = (1 / (1 + B))^2 * ((t : ℝ)^2 * (m / 16)) := by
      dsimp [d]
      ring
    _ ≤ s^2 * ((t : ℝ)^2 * (m / 16)) :=
      mul_le_mul_of_nonneg_right hsSq (by positivity)
    _ = s^2 * (t : ℝ)^2 * (m / 16) := by ring
    _ ≤ s^2 * (t : ℝ)^2 * (m / 8 - K * (t : ℝ)^2) := hSlope
    _ ≤ Mass t := hExact

/-- The TRUE finite-H Wilson action budget is strictly positive:
otherwise ZI's O(t) upper bound would force the already proved
genuine nonzero physical cancellation of ZF to vanish. -/
theorem p4Q2PZ37ZS_originalWilsonActionBudget_pos (H : ℕ) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  obtain ⟨delta, hdelta, hNonzero⟩ :=
    p4Q2PZ37ZF_originalPhysicalCancellation_ne_zero_smallPositive H
  by_contra hn
  have hZero : B = 0 := le_antisymm (le_of_not_gt hn) hB
  let t : Set.Ici (0 : ℝ) := ⟨delta / 2, by
    change (0 : ℝ) ≤ delta / 2
    linarith⟩
  have ht : 0 < (t : ℝ) := by
    change 0 < delta / 2
    positivity
  have htdelta : (t : ℝ) < delta := by
    change delta / 2 < delta
    linarith
  have hF : p4Q2PZ37ZE_originalPhysicalCancellation H t ≠ 0 :=
    hNonzero t ht htdelta
  have hNorm :
      ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ ≤ 2 * B * (t : ℝ) :=
    p4Q2PZ37ZI_originalPhysicalCancellation_norm_le_linearFine H t
  rw [hZero] at hNorm
  have hNormZero : ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ = 0 := by
    nlinarith [norm_nonneg (p4Q2PZ37ZE_originalPhysicalCancellation H t)]
  exact hF (norm_eq_zero.mp hNormZero)

/-- The authentic physical cancellation has an actual finite-H,b
FINE-UNIFORM POSITIVE GL RAYLEIGH FLOOR, though it remains extensively
H-dependent. No fine-zero Rayleigh limit, H-uniform coercivity, H1-H4
or continuum gap is inferred. -/
theorem p4Q2PZ37ZS_originalPhysicalGLRayleigh_exists_uniform_positiveFine
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧
      ∀ t : Set.Ici (0 : ℝ),
        0 < (t : ℝ) → (t : ℝ) < delta →
        c ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
          (p4Q2PZ37ZE_originalPhysicalCancellation H t) := by
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let F := p4Q2PZ37ZE_originalPhysicalCancellation H
  have hB : 0 < B := p4Q2PZ37ZS_originalWilsonActionBudget_pos H
  obtain ⟨delta₀, d, hd0, hd, hMass⟩ :=
    p4Q2PZ37ZS_originalPhysicalGLMass_exists_uniform_quadraticFine
      H b hb e e' left₀ right₀
  obtain ⟨delta₁, hd1, hNonzero⟩ :=
    p4Q2PZ37ZF_originalPhysicalCancellation_ne_zero_smallPositive H
  let delta := min delta₀ delta₁
  let c := d / (4 * B^2)
  have hdelta : 0 < delta := lt_min hd0 hd1
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨delta, c, hdelta, hc, ?_⟩
  intro t ht htDelta
  have ht0 : (t : ℝ) < delta₀ :=
    lt_of_lt_of_le htDelta (min_le_left _ _)
  have ht1 : (t : ℝ) < delta₁ :=
    lt_of_lt_of_le htDelta (min_le_right _ _)
  have hFNonzero : F t ≠ 0 := hNonzero t ht ht1
  have hNormPos : 0 < ‖F t‖^2 :=
    pow_pos (norm_pos_iff.mpr hFNonzero) 2
  have hMassLower :
      d * (t : ℝ)^2 ≤
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b hb.le (F t)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :=
    hMass t ht ht0
  have hNormUpper : ‖F t‖ ≤ 2 * B * (t : ℝ) :=
    p4Q2PZ37ZI_originalPhysicalCancellation_norm_le_linearFine H t
  have hNormSq : ‖F t‖^2 ≤ (2 * B * (t : ℝ))^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hNormUpper 2
  have hRatioBound : c * ‖F t‖^2 ≤ d * (t : ℝ)^2 := by
    calc
      c * ‖F t‖^2 ≤ c * (2 * B * (t : ℝ))^2 :=
        mul_le_mul_of_nonneg_left hNormSq hc.le
      _ = d * (t : ℝ)^2 := by
        dsimp [c]
        field_simp [ne_of_gt hB]
        ring
  change c ≤
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le (F t)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) / ‖F t‖^2
  exact (le_div_iff₀ hNormPos).2 (hRatioBound.trans hMassLower)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalPhysicalCancellation_eq_static_sub_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalStaticCoefficients_norm_sq_ge_WilsonComponent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalStaticPart_GL_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalScaledTaylorError_GL_le_quartic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalPhysicalGLMass_quadratic_minus_quartic_of_fixed_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalPhysicalGLMass_quadratic_minus_quartic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalRawInverseNorm_ge_budgetReciprocal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalPhysicalGLMass_exists_uniform_quadraticFine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalWilsonActionBudget_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZS_originalPhysicalGLRayleigh_exists_uniform_positiveFine
