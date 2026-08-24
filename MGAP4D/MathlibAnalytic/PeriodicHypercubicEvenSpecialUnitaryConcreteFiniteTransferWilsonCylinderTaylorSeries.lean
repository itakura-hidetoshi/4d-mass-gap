import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderMathlibContDiffInfinity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology ContDiff BigOperators

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

local instance wilsonCylinderTaylorSeriesPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- A quadratic operator-norm remainder gives the one-dimensional Mathlib
within-derivative on any set.  This generic statement is always consumed
immediately on the concrete operator space, so the canonical normed-space
instance path remains fixed throughout each calculus call. -/
private theorem wilsonCylinderTaylorSeries_hasDerivWithinAt_of_quadraticRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f f' : ℝ → E) (s : Set ℝ) (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (_hx : x ∈ s)
    (hrem : ∀ y ∈ s,
      ‖f y - f x - (y - x) • f' x‖ ≤ B * ‖y - x‖ ^ 2) :
    HasDerivWithinAt f (f' x) s x := by
  rw [hasDerivWithinAt_iff_tendsto]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro epsilon hepsilon
  let D := B + 1
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hBD : B ≤ D := by
    dsimp [D]
    linarith
  refine ⟨epsilon / D, div_pos hepsilon hD, ?_⟩
  intro y hy hdist
  by_cases hxy : y = x
  · subst y
    simp [hepsilon]
  · have hsub : y - x ≠ 0 := sub_ne_zero.mpr hxy
    have hnorm : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
    have hr := hrem y hy
    have hqnonneg :
        0 ≤ ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f' x‖ :=
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
    have hdx : ‖y - x‖ < epsilon / D := by
      simpa [Real.dist_eq] using hdist
    have hq :
        ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f' x‖ < epsilon := by
      calc
        ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f' x‖ ≤
            ‖y - x‖⁻¹ * (B * ‖y - x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (norm_nonneg _))
        _ = B * ‖y - x‖ := by
          field_simp [hnorm]
        _ ≤ D * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right hBD (norm_nonneg _)
        _ < D * (epsilon / D) :=
          mul_lt_mul_of_pos_left hdx hD
        _ = epsilon := by
          field_simp [ne_of_gt hD]
    simpa [Real.dist_eq, abs_of_nonneg hqnonneg] using hq

/-- Exact first derivative of every Wilson insertion family on a nondegenerate
compact forward physical coupling interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_derivWithin_Icc
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma)
    (ht : t ∈ Set.Icc beta gamma) :
    derivWithin
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (Set.Icc beta gamma) t =
      -periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN (m + 1) t := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ (m + 2)
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := pow_nonneg hC (m + 2)
  have ht0 : 0 ≤ t := hbeta.trans ht.1
  have hraw :=
    wilsonCylinderTaylorSeries_hasDerivWithinAt_of_quadraticRemainder
      (f := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (f' := fun u =>
        -periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + 1) u)
      (s := Set.Icc beta gamma) B hB t ht
      (by
        intro y hy
        have hy0 : 0 ≤ y := hbeta.trans hy.1
        simpa [B, C] using
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_quadraticRemainder
            H N hN m t y ht0 hy0)
  exact hraw.derivWithin ((uniqueDiffOn_Icc hbg) t ht)

/-- The compact-interval iterated derivative hierarchy is literal:
`D^n O_m = (-1)^n O_(m+n)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_iteratedDerivWithin_Icc
    (H N : ℕ) (hN : 0 < N) (m n : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma)
    (ht : t ∈ Set.Icc beta gamma) :
    iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (Set.Icc beta gamma) t =
      ((-1 : ℝ) ^ n) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + n) t := by
  induction n generalizing t with
  | zero =>
      simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hEqOn :
          Set.EqOn
            (iteratedDerivWithin n
              (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
                H N hN m)
              (Set.Icc beta gamma))
            (fun u : ℝ =>
              ((-1 : ℝ) ^ n) •
                periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
                  H N hN (m + n) u)
            (Set.Icc beta gamma) := by
        intro u hu
        exact ih u hu
      rw [derivWithin_congr hEqOn (ih t ht)]
      rw [derivWithin_fun_const_smul_field]
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_derivWithin_Icc
        H N hN (m + n) beta gamma t hbeta hbg ht]
      rw [smul_neg]
      have hidx : m + n + 1 = m + (n + 1) := by omega
      rw [hidx]
      have hsign : (-1 : ℝ) ^ (n + 1) = - ((-1 : ℝ) ^ n) := by
        rw [pow_succ]
        ring
      rw [hsign, neg_smul]

/-- The transfer family itself has the expected literal compact-interval
iterated derivatives. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma)
    (ht : t ∈ Set.Icc beta gamma) :
    iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      (Set.Icc beta gamma) t =
      ((-1 : ℝ) ^ n) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n t (hbeta.trans ht.1) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_iteratedDerivWithin_Icc
    H N hN 0 n beta gamma t hbeta hbg ht]
  simp only [Nat.zero_add]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_of_nonneg
    H N hN n t (hbeta.trans ht.1)]

/-- Uniform norm bound for all compact-interval transfer derivatives. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc_norm_le
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma)
    (ht : t ∈ Set.Icc beta gamma) :
    ‖iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      (Set.Icc beta gamma) t‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ n := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc
    H N hN n beta gamma t hbeta hbg ht]
  calc
    ‖((-1 : ℝ) ^ n) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n t (hbeta.trans ht.1)‖ ≤
      ‖((-1 : ℝ) ^ n)‖ *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n t (hbeta.trans ht.1)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n t (hbeta.trans ht.1)‖ := by
      rw [norm_pow]
      simp
    _ ≤ periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ n :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_le
        H N hN n t (hbeta.trans ht.1)

/-- The physical Wilson Taylor term based at `beta` and evaluated at `gamma`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : ℝ) (k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  (((k.factorial : ℝ)⁻¹ * (gamma - beta) ^ k) •
    (((-1 : ℝ) ^ k) •
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN k beta hbeta))

/-- Mathlib's interval Taylor polynomial is exactly the finite sum of literal
Wilson insertion terms. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_taylorWithinEval_eq_WilsonTaylorSum
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hbg : beta < gamma) :
    taylorWithinEval
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      n (Set.Icc beta gamma) beta gamma =
      ∑ k ∈ Finset.range (n + 1),
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta gamma k := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc
    H N hN k beta gamma beta hbeta hbg (left_mem_Icc.mpr hbg.le)]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
  rfl

/-- All-order forward Taylor remainder bound in operator norm on the genuine
physical coupling half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN gamma -
        ∑ k ∈ Finset.range (n + 1),
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta gamma k‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ (n + 1) * (gamma - beta) ^ (n + 1) / n.factorial := by
  rcases hbg.eq_or_lt with hEq | hlt
  · subst gamma
    have hO0 :
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN 0 beta hbeta =
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta := by
      exact
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_zero_eq_transferOperator
          H N hN beta hbeta).trans
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_eq_physicalTransfer
          H N hN beta hbeta).symm
    have hterm0 :
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta beta 0 =
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta := by
      unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
      simpa [hO0]
    have hsum :
        (∑ k ∈ Finset.range (n + 1),
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta beta k) =
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta := by
      rw [← hterm0]
      apply Finset.sum_eq_single 0
      · intro b hb hb0
        unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
        simp [hb0]
      · simp
    rw [hsum]
    simp
  · have hsubset : Set.Icc beta gamma ⊆ Set.Ici (0 : ℝ) := by
      intro y hy
      exact hbeta.trans hy.1
    have hCfinite :
        ContDiffOn ℝ (n + 1 : ℕ)
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN)
          (Set.Icc beta gamma) := by
      have hinfty :=
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_contDiffOn_infty
          H N hN
      exact (hinfty.of_le (by simp)).mono hsubset
    have hderiv : ∀ y ∈ Set.Icc beta gamma,
        ‖iteratedDerivWithin (n + 1)
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN)
          (Set.Icc beta gamma) y‖ ≤
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ (n + 1) := by
      intro y hy
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc_norm_le
          H N hN (n + 1) beta gamma y hbeta hlt hy
    have hTaylor := taylor_mean_remainder_bound hlt.le hCfinite
      (right_mem_Icc.mpr hlt.le) hderiv
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_taylorWithinEval_eq_WilsonTaylorSum
      H N hN n beta gamma hbeta hlt] at hTaylor
    exact hTaylor

/-- Each Wilson Taylor term is bounded by the corresponding scalar exponential
majorant with argument `C * (gamma-beta)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_norm_le_expMajorant
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma) (k : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
        H N hN beta hbeta gamma k‖ ≤
      (k.factorial : ℝ)⁻¹ *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N * (gamma - beta)) ^ k := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let a : ℝ := (k.factorial : ℝ)⁻¹ * (gamma - beta) ^ k
  let s : ℝ := (-1 : ℝ) ^ k
  have hdelta : 0 ≤ gamma - beta := sub_nonneg.mpr hbg
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity) (pow_nonneg hdelta k)
  have hna : ‖a‖ = a := by
    simpa [Real.norm_eq_abs, abs_of_nonneg ha]
  have hns : ‖s‖ = 1 := by
    dsimp [s]
    simp [Real.norm_eq_abs, abs_pow]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
  change ‖a •
      (s • periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN k beta hbeta)‖ ≤ _
  calc
    ‖a •
        (s • periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN k beta hbeta)‖ ≤
      ‖a‖ *
        ‖s • periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN k beta hbeta‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖a‖ *
        (‖s‖ *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN k beta hbeta‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_smul_le _ _) (norm_nonneg _)
    _ = a *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN k beta hbeta‖ := by
      rw [hna, hns, one_mul]
    _ ≤ a * C ^ k :=
      mul_le_mul_of_nonneg_left
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_le
          H N hN k beta hbeta) ha
    _ = (k.factorial : ℝ)⁻¹ * (C * (gamma - beta)) ^ k := by
      dsimp [a]
      rw [mul_pow]
      ring
    _ = _ := by rfl

/-- The operator-valued Wilson Taylor series is absolutely summable for every
forward physical coupling displacement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_summable_norm
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma) :
    Summable (fun k : ℕ =>
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
        H N hN beta hbeta gamma k‖) := by
  let x : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N * (gamma - beta)
  have hmajor : Summable (fun k : ℕ => (k.factorial : ℝ)⁻¹ * x ^ k) := by
    simpa [smul_eq_mul] using
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) x)
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hmajor
  intro k
  simpa [x] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_norm_le_expMajorant
      H N hN beta gamma hbeta hbg k

/-- The explicit scalar Taylor-remainder majorant tends to zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainderMajorant_tendsto_zero
    (H N : ℕ) (beta gamma : ℝ) (_hbg : beta ≤ gamma) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N ^ (n + 1) * (gamma - beta) ^ (n + 1) / n.factorial)
      atTop (𝓝 0) := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let d := gamma - beta
  let x := C * d
  have hExpSummable : Summable (fun n : ℕ => (n.factorial : ℝ)⁻¹ * x ^ n) := by
    simpa [smul_eq_mul] using
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) x)
  have hExpTerm : Tendsto (fun n : ℕ => (n.factorial : ℝ)⁻¹ * x ^ n) atTop (𝓝 0) :=
    hExpSummable.tendsto_atTop_zero
  have hMul : Tendsto (fun n : ℕ => x * ((n.factorial : ℝ)⁻¹ * x ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hExpTerm)
  have hEq :
      (fun n : ℕ => C ^ (n + 1) * d ^ (n + 1) / n.factorial) =
        (fun n : ℕ => x * ((n.factorial : ℝ)⁻¹ * x ^ n)) := by
    funext n
    dsimp [x]
    rw [pow_succ, pow_succ, div_eq_mul_inv, mul_pow]
    ring
  change Tendsto (fun n : ℕ => C ^ (n + 1) * d ^ (n + 1) / n.factorial) atTop (𝓝 0)
  rw [hEq]
  exact hMul

/-- The finite Wilson Taylor sums converge in operator norm to the physical
transfer operator at every forward physical coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_partialSums_tendsto_transfer
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta gamma k)
      atTop
      (𝓝 (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN gamma)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hmajor :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainderMajorant_tendsto_zero
      H N beta gamma hbg
  rw [Metric.tendsto_atTop] at hmajor
  rcases hmajor epsilon hepsilon with ⟨N0, hN0⟩
  refine ⟨N0, fun n hn => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt
    (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le
      H N hN n beta gamma hbeta hbg)
    (by simpa [Real.dist_eq] using hN0 n hn)

/-- Exact operator-valued Taylor series for the positive-half physical transfer.
The equality is a genuine operator-norm `HasSum` statement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_hasSum_transfer
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma) :
    HasSum
      (fun k : ℕ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta gamma k)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN gamma) := by
  have hnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_summable_norm
      H N hN beta gamma hbeta hbg
  have hs :
      Tendsto (fun n : ℕ => Finset.range (n + 1)) atTop atTop :=
    tendsto_finset_range.comp (tendsto_add_atTop_nat 1)
  have hpartial :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_partialSums_tendsto_transfer
      H N hN beta gamma hbeta hbg
  exact hasSum_of_subseq_of_summable hnorm hs hpartial

/-- Final forward Taylor-series package: quantitative remainder, absolute
summability, norm convergence, and exact series reconstruction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorSeries_package
    (H N : ℕ) (hN : 0 < N) :
    ∀ (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma),
      (∀ n : ℕ,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN gamma -
            ∑ k ∈ Finset.range (n + 1),
              periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
                H N hN beta hbeta gamma k‖ ≤
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N ^ (n + 1) * (gamma - beta) ^ (n + 1) / n.factorial) ∧
      Summable (fun k : ℕ =>
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta gamma k‖) ∧
      HasSum
        (fun k : ℕ =>
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta gamma k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN gamma) := by
  intro beta gamma hbeta hbg
  exact ⟨
    fun n =>
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le
        H N hN n beta gamma hbeta hbg,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_summable_norm
      H N hN beta gamma hbeta hbg,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_hasSum_transfer
      H N hN beta gamma hbeta hbg⟩

end
end MathlibAnalytic
end MGAP4D