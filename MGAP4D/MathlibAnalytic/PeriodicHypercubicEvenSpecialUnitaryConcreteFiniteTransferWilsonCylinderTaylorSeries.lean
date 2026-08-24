import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderMathlibContDiffInfinity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Algebra.Exponential
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

/-- Restrict the native Wilson insertion derivative from the physical half-line
`Ici 0` to a compact forward coupling interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_hasDerivWithinAt_Icc
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (ht : t ∈ Set.Icc beta gamma) :
    HasDerivWithinAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN (m + 1) t)
      (Set.Icc beta gamma) t := by
  have ht0 : t ∈ Set.Ici (0 : ℝ) := hbeta.trans ht.1
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_hasDerivWithinAt
      H N hN m t ht0).mono (fun y hy => hbeta.trans hy.1)

/-- Exact first derivative on a nondegenerate compact physical coupling interval. -/
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
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_hasDerivWithinAt_Icc
      H N hN m beta gamma t hbeta ht).derivWithin
      ((uniqueDiffOn_Icc hbg) t ht)

/-- Every compact forward interval inherits the full insertion hierarchy:
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
  | zero => simp
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
      let F :=
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + n)
      let c : ℝ := (-1 : ℝ) ^ n
      have hbase :=
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_hasDerivWithinAt_Icc
          H N hN (m + n) beta gamma t hbeta ht
      have hunique : UniqueDiffWithinAt ℝ (Set.Icc beta gamma) t :=
        (uniqueDiffOn_Icc hbg) t ht
      have hscaled0 := (hbase.const_smul c).derivWithin hunique
      have hscaled :
          derivWithin (fun u : ℝ => c • F u) (Set.Icc beta gamma) t =
            c • (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
              H N hN (m + n + 1) t) := by
        simpa only [Pi.smul_apply] using hscaled0
      change derivWithin (fun u : ℝ => c • F u) (Set.Icc beta gamma) t = _
      rw [hscaled, smul_neg]
      dsimp [c]
      have hidx : m + n + 1 = m + (n + 1) := by omega
      rw [hidx]
      have hsign : (-1 : ℝ) ^ (n + 1) = - ((-1 : ℝ) ^ n) := by
        rw [pow_succ]
        ring
      rw [hsign]
      exact (neg_smul ((-1 : ℝ) ^ n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + (n + 1)) t)).symm

/-- The transfer family itself has the expected literal interval derivatives. -/
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

/-- Uniform derivative norm bound on every compact forward coupling interval. -/
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
  rw [norm_smul]
  have hsign : ‖((-1 : ℝ) ^ n)‖ = 1 := by
    rw [norm_pow]
    simp
  rw [hsign, one_mul]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_le
      H N hN n t (hbeta.trans ht.1)

/-- The physical Taylor term based at `beta` and evaluated at `gamma`.
Its coefficient is the standard Taylor coefficient and its operator factor is
the literal order-`k` Wilson action insertion. -/
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
    simp [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm]
  · have hsubset : Set.Icc beta gamma ⊆ Set.Ici (0 : ℝ) :=
      fun x hx => hbeta.trans hx.1
    have hCinfty :
        ContDiffOn ℝ ∞
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN)
          (Set.Icc beta gamma) :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_contDiffOn_infty
        H N hN).mono hsubset
    have hCfinite :
        ContDiffOn ℝ (n + 1 : ℕ)
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN)
          (Set.Icc beta gamma) :=
      hCinfty.of_le (by simp)
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
    have hTaylor := taylor_mean_remainder_bound hbg hCfinite
      (right_mem_Icc.mpr hbg) hderiv
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
  have hC : 0 ≤ C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg
      H N
  have hdelta : 0 ≤ gamma - beta := sub_nonneg.mpr hbg
  have hcoef : 0 ≤ (k.factorial : ℝ)⁻¹ * (gamma - beta) ^ k :=
    mul_nonneg (by positivity) (pow_nonneg hdelta k)
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
  rw [norm_smul, norm_smul]
  have hsign : ‖((-1 : ℝ) ^ k)‖ = 1 := by
    rw [norm_pow]
    simp
  rw [hsign, one_mul, Real.norm_eq_abs, abs_of_nonneg hcoef]
  calc
    ((k.factorial : ℝ)⁻¹ * (gamma - beta) ^ k) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN k beta hbeta‖ ≤
      ((k.factorial : ℝ)⁻¹ * (gamma - beta) ^ k) * C ^ k :=
        mul_le_mul_of_nonneg_left
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_le
            H N hN k beta hbeta) hcoef
    _ = (k.factorial : ℝ)⁻¹ * (C * (gamma - beta)) ^ k := by
      rw [mul_pow]
      ring

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
  apply Summable.of_norm_bounded hmajor
  intro k
  rw [Real.norm_of_nonneg]
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_norm_le_expMajorant
        H N hN beta gamma hbeta hbg k
  · exact mul_nonneg (by positivity) (pow_nonneg (mul_nonneg
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N)
      (sub_nonneg.mpr hbg)) k)

/-- The explicit scalar Taylor-remainder majorant tends to zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainderMajorant_tendsto_zero
    (H N : ℕ) (beta gamma : ℝ) (hbg : beta ≤ gamma) :
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
  simpa [C, d, x, pow_succ, div_eq_mul_inv, mul_pow] using hMul

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
  rw [dist_eq_norm]
  rw [norm_sub_rev]
  exact lt_of_le_of_lt
    (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le
      H N hN n beta gamma hbeta hbg)
    (by simpa [Real.dist_eq] using hN0 n hn)

/-- Exact operator-valued Taylor series for the positive-half physical transfer.
The equality is a genuine `HasSum` statement, not only convergence of a custom
certificate. -/
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
  apply hasSum_of_subseq_of_summable hnorm
    (s := fun n : ℕ => Finset.range (n + 1))
  · exact tendsto_finset_range.comp (tendsto_add_atTop_nat 1)
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_partialSums_tendsto_transfer
        H N hN beta gamma hbeta hbg

/-- Final forward Taylor-series package: quantitative remainder, absolute
summability, norm convergence, and exact series reconstruction of the genuine
physical transfer operator. -/
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
