import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalBetaZeroRankOneTopV5_PZ37ANQ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANR — actual Wilson vacuum stability and fixed-Haar first response

The genuine physical Gauss-law one-slab Wilson transfer is a rank-one
projection P at beta=0 (ANQ), with the original positive unit top state c.
The unchanged transfer T_beta has the actual-model Lipschitz constant C_H
on the nonnegative beta half-line. We establish:

  ||T_beta|| * ||Omega_beta - c|| <= 2 C_H beta.

No eigenvector analyticity, perturbative Kato assumptions, or chosen
eigenvector continuity is assumed; positivity fixes the sign. Then
replacing the true vacuum Omega_beta by the fixed original Haar state c
in the FIRST original Wilson-mode transfer response has a remainder
bounded by 2(C_H beta)^2 after multiplying by ||T_beta||. Thus the genuine
first-order Wilson overlap is reduced to the original fixed-Haar operator
response without postulating that this response is nonzero.

These are finite-volume model theorems, not uniform-in-H gap theorems, OS
boundary operator identification, or continuum 4D Yang--Mills.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANR_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANR_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANR_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANR_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANR_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ANR_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Generic real Hilbert-space rank-one perturbation stability.
If T Ω = ||T|| Ω and U Ω = <c,Ω> c, where c,Ω are unit and
<c,Ω> >= 0, then the signed top-state displacement obeys
||T|| ||Ω-c|| <= 2||T-U||. No assumption of eigenvector
differentiability, spectral analyticity, or strict gap of T. -/
theorem p4Q2PZ37ANR_realHilbert_rankOne_topVacuum_distance_mul_le_twoPerturbation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T U : E →L[ℝ] E) (Ω c : E)
    (hΩ : ‖Ω‖ = 1) (hc : ‖c‖ = 1)
    (heigen : T Ω = ‖T‖ • Ω)
    (hrank : U Ω = (inner ℝ c Ω) • c)
    (hpositive : 0 ≤ inner ℝ c Ω) :
    ‖T‖ * ‖Ω - c‖ ≤ 2 * ‖T - U‖ := by
  let a : ℝ := inner ℝ c Ω
  have hnormT : 0 ≤ ‖T‖ := norm_nonneg T
  have ha : 0 ≤ a := hpositive
  have hdiff : (T - U) Ω = ‖T‖ • Ω - a • c := by
    rw [ContinuousLinearMap.sub_apply, heigen, hrank]
  have hpert : ‖‖T‖ • Ω - a • c‖ ≤ ‖T - U‖ := by
    have h := (T - U).le_opNorm Ω
    rw [hdiff, hΩ, mul_one] at h
    exact h
  have hnormOmega : ‖(‖T‖ : ℝ) • Ω‖ = ‖T‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnormT, hΩ, mul_one]
  have hnormC : ‖a • c‖ = a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, hc, mul_one]
  have hdiffNorm : |‖T‖ - a| ≤ ‖‖T‖ • Ω - a • c‖ := by
    have h := abs_norm_sub_norm_le ((‖T‖ : ℝ) • Ω) (a • c)
    rw [hnormOmega, hnormC] at h
    exact h
  have hdecomp :
      (‖T‖ : ℝ) • (Ω - c) =
        ((‖T‖ : ℝ) • Ω - a • c) + (a - ‖T‖) • c := by
    simp only [smul_sub, sub_smul]
    abel
  have hlast : ‖(a - ‖T‖) • c‖ = |‖T‖ - a| := by
    rw [norm_smul, Real.norm_eq_abs, hc, mul_one, abs_sub_comm]
  calc
    ‖T‖ * ‖Ω - c‖ = ‖(‖T‖ : ℝ) • (Ω - c)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnormT]
    _ = ‖((‖T‖ : ℝ) • Ω - a • c) + (a - ‖T‖) • c‖ := by
      rw [hdecomp]
    _ ≤ ‖(‖T‖ : ℝ) • Ω - a • c‖ + ‖(a - ‖T‖) • c‖ :=
      norm_add_le _ _
    _ ≤ ‖T - U‖ + ‖T - U‖ := by
      apply add_le_add hpert
      rw [hlast]
      exact hdiffNorm.trans hpert
    _ = 2 * ‖T - U‖ := by ring

/-- True SU(2) physical Wilson vacuum at finite H is quantitatively
Lipschitz-at-zero in Hilbert norm, measured against the ACTUAL normalized
Gauss-law Haar constant vector. No continuity of a choice operator
was smuggled into the proof. -/
theorem p4Q2PZ37ANR_originalPhysicalVacuum_distance_weighted_le_twoBudgetBeta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2‖ ≤
      2 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hΩ : ‖Ω‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) beta hbeta
  have hc : ‖c‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have heigen : T Ω = ‖T‖ • Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta
  have hrank : U Ω = (inner ℝ c Ω) • c :=
    p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_eq_haarRankOne H Ω
  have hpositive : 0 ≤ inner ℝ c Ω := by
    have h :=
      p4Q2PZ37ANM_originalPhysicalTop_inner_modeZero_pos H beta hbeta
    rw [p4Q2PZ37ANM_actualModeZero_eq_physicalConstant] at h
    rw [real_inner_comm]
    exact le_of_lt h
  have hpert :
      ‖T - U‖ ≤ C * beta := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
        H 2 (by norm_num) 0 beta (by norm_num) hbeta
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbeta] using h
  calc
    ‖T‖ * ‖Ω - c‖ ≤ 2 * ‖T - U‖ :=
      p4Q2PZ37ANR_realHilbert_rankOne_topVacuum_distance_mul_le_twoPerturbation
        T U Ω c hΩ hc heigen hrank hpositive
    _ ≤ 2 * (C * beta) := mul_le_mul_of_nonneg_left hpert (by norm_num)

/-- The actual top-vacuum displacement has an explicit bound for
C_H beta<1 (and hence converges to zero at least linearly at beta=0).
No norm of the unknown top transfer remains in the denominator. -/
theorem p4Q2PZ37ANR_originalPhysicalVacuum_explicitSmallBeta_distance_bound
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta < 1) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta -
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2‖ ≤
      (2 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta)) /
      (1 - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) := by
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have htoppos : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  have hdenompos : 0 < 1 - C * beta := sub_pos.mpr hsmall
  have htoplower : 1 - C * beta ≤ ‖T‖ :=
    p4Q2PZ37ANQ_originalPhysicalTopNorm_ge_one_sub_budgetBeta H beta hbeta
  have hnumpos : 0 ≤ 2 * (C * beta) := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H)
        hbeta)
  have hweighted :
      ‖T‖ * ‖Ω - c‖ ≤ 2 * (C * beta) :=
    p4Q2PZ37ANR_originalPhysicalVacuum_distance_weighted_le_twoBudgetBeta
      H beta hbeta
  have hdiv : ‖Ω - c‖ ≤ (2 * (C * beta)) / ‖T‖ := by
    apply (le_div_iff₀ htoppos).2
    calc
      ‖Ω - c‖ * ‖T‖ = ‖T‖ * ‖Ω - c‖ := mul_comm _ _
      _ ≤ _ := hweighted
  calc
    ‖Ω - c‖ ≤ 2 * (C * beta) / ‖T‖ := hdiv
    _ ≤ 2 * (C * beta) / (1 - C * beta) := by
      apply (div_le_div_iff₀ htoppos hdenompos).2
      exact mul_le_mul_of_nonneg_left htoplower hnumpos

/-- Exact perturbative identity for the TRUE top/first-mode coefficient:
after using the beta-zero rank-one annihilation, its difference from the
fixed-original-Haar-vacuum response is the (T_beta-T_0) matrix element of
Omega_beta-c, bounded by the product of the operator perturbation norm and
the true vacuum displacement. No beta derivative is yet postulated. -/
theorem p4Q2PZ37ANR_originalTopFirstMode_fixedHaarResponse_error_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    |‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) -
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) 0 (by norm_num))
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)| ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) 0 (by norm_num)‖ *
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have heigen : T Ω = ‖T‖ • Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta
  have hUzero : inner ℝ (U Ω) v1 = 0 :=
    p4Q2PZ37ANP_originalPhysicalBetaZero_allInput_modeOne_inner_zero H Ω
  have hv1 : ‖v1‖ = 1 :=
    (p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal H).1 1
  have heq : ‖T‖ * inner ℝ Ω v1 = inner ℝ ((T - U) Ω) v1 := by
    calc
      ‖T‖ * inner ℝ Ω v1 = inner ℝ (T Ω) v1 := by
        rw [heigen]
        exact (real_inner_smul_left Ω v1 ‖T‖).symm
      _ = inner ℝ ((T - U) Ω) v1 := by
        rw [ContinuousLinearMap.sub_apply, inner_sub_left, hUzero, sub_zero]
  have hdiff :
      ‖T‖ * inner ℝ Ω v1 - inner ℝ ((T - U) c) v1 =
        inner ℝ ((T - U) (Ω - c)) v1 := by
    rw [heq, map_sub, inner_sub_left]
  have hCS :
      |inner ℝ ((T - U) (Ω - c)) v1| ≤
        ‖(T - U) (Ω - c)‖ * ‖v1‖ :=
    abs_real_inner_le_norm _ _
  have hop : ‖(T - U) (Ω - c)‖ ≤ ‖T - U‖ * ‖Ω - c‖ :=
    (T - U).le_opNorm (Ω - c)
  calc
    |‖T‖ * inner ℝ Ω v1 - inner ℝ ((T - U) c) v1| =
        |inner ℝ ((T - U) (Ω - c)) v1| := congrArg abs hdiff
    _ ≤ ‖(T - U) (Ω - c)‖ * ‖v1‖ := hCS
    _ ≤ (‖T - U‖ * ‖Ω - c‖) * ‖v1‖ :=
      mul_le_mul_of_nonneg_right hop (norm_nonneg v1)
    _ = ‖T - U‖ * ‖Ω - c‖ := by rw [hv1, mul_one]

/-- The genuinely beta-dependent Wilson vacuum can be replaced in the
first-Wilson-mode RESPONSE by the unchanged physical Haar vacuum with an
EXPLICIT O(beta^2) remainder. The input is the TRUE one-slab Wilson
operator in both terms, not an abstract or OS surrogate. -/
theorem p4Q2PZ37ANR_originalTopFirstMode_fixedHaarResponse_weightedError_le_quadratic
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
      |‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta‖ *
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H 2 (by norm_num) beta hbeta)
          (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) -
        inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) beta hbeta -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) 0 (by norm_num))
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
          (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)| ≤
      2 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta)^2 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hcoef :
      |‖T‖ * inner ℝ Ω v1 - inner ℝ ((T - U) c) v1| ≤
        ‖T - U‖ * ‖Ω - c‖ :=
    p4Q2PZ37ANR_originalTopFirstMode_fixedHaarResponse_error_le H beta hbeta
  have hpert : ‖T - U‖ ≤ C * beta := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
        H 2 (by norm_num) 0 beta (by norm_num) hbeta
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbeta] using h
  have hdist :
      ‖T‖ * ‖Ω - c‖ ≤ 2 * (C * beta) :=
    p4Q2PZ37ANR_originalPhysicalVacuum_distance_weighted_le_twoBudgetBeta
      H beta hbeta
  have hnumpos : 0 ≤ 2 * (C * beta) := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H)
        hbeta)
  calc
    ‖T‖ * |‖T‖ * inner ℝ Ω v1 - inner ℝ ((T - U) c) v1| ≤
        ‖T‖ * (‖T - U‖ * ‖Ω - c‖) :=
      mul_le_mul_of_nonneg_left hcoef (norm_nonneg T)
    _ = ‖T - U‖ * (‖T‖ * ‖Ω - c‖) := by ring
    _ ≤ ‖T - U‖ * (2 * (C * beta)) :=
      mul_le_mul_of_nonneg_left hdist (norm_nonneg (T - U))
    _ ≤ (C * beta) * (2 * (C * beta)) :=
      mul_le_mul_of_nonneg_right hpert hnumpos
    _ = 2 * (C * beta)^2 := by ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANR_realHilbert_rankOne_topVacuum_distance_mul_le_twoPerturbation
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANR_originalPhysicalVacuum_distance_weighted_le_twoBudgetBeta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANR_originalPhysicalVacuum_explicitSmallBeta_distance_bound
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANR_originalTopFirstMode_fixedHaarResponse_error_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANR_originalTopFirstMode_fixedHaarResponse_weightedError_le_quadratic
