import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2TopFirstModeRawKernelOverlapV5_PZ37ANO
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANP — finite-volume quantitative Wilson vacuum/first-mode overlap

The exact physical first Wilson Gauss-law mode is Haar-centered. ANO shows
the original beta=0 two-boundary Wilson kernel is the rank-one constant
kernel. Consequently every physical input maps under the beta=0 transfer
orthogonally to the first native Wilson mode.

Combine this true-model rank-one vanishing with the already-certified
operator-norm beta-Lipschitz bound for the SAME original physical one-slab
transfer. No continuity or analyticity of the selected top eigenvector is
assumed. For every finite H and beta >= 0 the unnormalized top/first-mode
overlap has absolute value at most the original global action budget times
beta. The normalized overlap has the corresponding positive-transfer-norm
denominator.

This is a quantitative beta-zero obstruction only, not a proof of
nonzero overlap for beta>0, OS realization, volume-uniform gap or 4D
continuum Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANP_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANP_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANP_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANP_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANP_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ37ANP_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2PZ37ANP_spatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  infer_instance

/-- A generic norm perturbation lemma: a normalized top eigenvector cannot
have a large overlap with a unit test vector annihilated by the reference
operator's matrix coefficient. No perturbative eigenvector-choice assumption. -/
theorem p4Q2PZ37ANP_realHilbert_topOverlap_le_operatorPerturbation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T U : E →L[ℝ] E) (Ω v : E)
    (hΩ : ‖Ω‖ = 1) (hv : ‖v‖ = 1)
    (heigen : T Ω = ‖T‖ • Ω)
    (hnull : inner ℝ (U Ω) v = 0) :
    |‖T‖ * inner ℝ Ω v| ≤ ‖T - U‖ := by
  have hcoeff :
      ‖T‖ * inner ℝ Ω v = inner ℝ ((T - U) Ω) v := by
    calc
      ‖T‖ * inner ℝ Ω v = inner ℝ (T Ω) v := by
        rw [heigen]
        exact (real_inner_smul_left Ω v ‖T‖).symm
      _ = inner ℝ ((T - U) Ω) v := by
        rw [ContinuousLinearMap.sub_apply, inner_sub_left, hnull, sub_zero]
  calc
    |‖T‖ * inner ℝ Ω v| = |inner ℝ ((T - U) Ω) v| :=
      congrArg abs hcoeff
    _ ≤ ‖(T - U) Ω‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖T - U‖ * ‖Ω‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right ((T - U).le_opNorm Ω) (norm_nonneg v)
    _ = ‖T - U‖ := by rw [hΩ, hv]; ring

/-- The ACTUAL zero-coupling physical one-slab Wilson transfer has no
first-mode matrix coefficient for ANY original physical Gauss-law input.
The zero-mode Haar centering is inherited from the original ANM/ANI data,
and the kernel factorization is ANO's exact original pair-Haar L² result. -/
theorem p4Q2PZ37ANP_originalPhysicalBetaZero_allInput_modeOne_inner_zero
    (H : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) 0 (by norm_num) f)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) = 0 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let c : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  let v1 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have h01 :
      inner ℝ (p4Q2PZ37AMU_actualPhysicalGaussMode H 0)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) = 0 :=
    (p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal H).inner_eq_zero
      (by decide : (0 : ℕ) ≠ 1)
  rw [p4Q2PZ37ANM_actualModeZero_eq_physicalConstant] at h01
  have hcenter : inner ℝ c (v1 : Lp ℝ 2 μ) = 0 := h01
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) 0 (by norm_num) f) v1 =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H 2 (by norm_num) 0 (by norm_num))
        (f : Lp ℝ 2 μ) (v1 : Lp ℝ 2 μ) := by
          change
            inner ℝ
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
                H 2 (by norm_num) 0 (by norm_num) (f : Lp ℝ 2 μ))
              (v1 : Lp ℝ 2 μ) = _
          exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
            H 2 (by norm_num) 0 (by norm_num) f v1
    _ = inner ℝ c (f : Lp ℝ 2 μ) * inner ℝ c (v1 : Lp ℝ 2 μ) := by
          rw [p4Q2PZ37ANO_originalOneSlabPairKernel_betaZero_eq_oneTensor]
          exact realL2HilbertSchmidtKernelPairing_externalTensor
            c (f : Lp ℝ 2 μ) c (v1 : Lp ℝ 2 μ)
    _ = 0 := by rw [hcenter, mul_zero]

/-- The genuine physical top/first-Wilson-mode coefficient obeys a
quantitative small-coupling upper bound in EVERY finite volume H.
The original Wilson action budget is the exact existing finite-slab bound,
not an abstract perturbation constant. -/
theorem p4Q2PZ37ANP_originalPhysicalTopModeOne_weightedAbs_le_budgetBeta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    |‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H * beta := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have hΩ : ‖Ω‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) beta hbeta
  have hv1 : ‖v1‖ = 1 :=
    (p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal H).1 1
  have heigen : T Ω = ‖T‖ • Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta
  have hnull : inner ℝ (U Ω) v1 = 0 :=
    p4Q2PZ37ANP_originalPhysicalBetaZero_allInput_modeOne_inner_zero H Ω
  have hbound :
      ‖T - U‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
        H 2 (by norm_num) 0 beta (by norm_num) hbeta
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbeta] using h
  calc
    |‖T‖ * inner ℝ Ω v1| ≤ ‖T - U‖ :=
      p4Q2PZ37ANP_realHilbert_topOverlap_le_operatorPerturbation
        T U Ω v1 hΩ hv1 heigen hnull
    _ ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta := hbound

/-- Dividing by the actual strictly positive Wilson top transfer norm
bounds the unnormalized physical top/first-mode overlap itself. This is an
upper bound, not a witness of nonvanishing at any beta>0. -/
theorem p4Q2PZ37ANP_originalPhysicalTopModeOne_abs_le_budgetBeta_div_topNorm
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    |inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) /
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H 2 (by norm_num) beta hbeta
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have hpos : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  have hbound :=
    p4Q2PZ37ANP_originalPhysicalTopModeOne_weightedAbs_le_budgetBeta
      H beta hbeta
  have hmul :
      ‖T‖ * |inner ℝ Ω v1| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta := by
    simpa only [abs_mul, abs_of_nonneg (le_of_lt hpos)] using hbound
  exact (le_div_iff₀ hpos).2 hmul

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANP_realHilbert_topOverlap_le_operatorPerturbation
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANP_originalPhysicalBetaZero_allInput_modeOne_inner_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANP_originalPhysicalTopModeOne_weightedAbs_le_budgetBeta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANP_originalPhysicalTopModeOne_abs_le_budgetBeta_div_topNorm
