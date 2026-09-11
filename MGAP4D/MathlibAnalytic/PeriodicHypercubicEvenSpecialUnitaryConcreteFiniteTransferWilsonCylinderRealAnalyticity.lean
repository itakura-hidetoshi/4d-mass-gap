import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderTaylorSeries
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology ContDiff BigOperators Pointwise Interval ENNReal

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 500000

local instance wilsonCylinderRealAnalyticityPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

private theorem wilsonCylinderRealAnalyticity_uIcc_subset_Ici
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) :
    Set.uIcc beta gamma ⊆ Set.Ici (0 : ℝ) := by
  intro t ht
  rw [Set.mem_Ici]
  rw [Set.mem_uIcc] at ht
  rcases ht with h | h
  · exact hbeta.trans h.1
  · exact hgamma.trans h.1

private theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_uIcc_at_left
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hne : beta ≠ gamma) :
    iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      (Set.uIcc beta gamma) beta =
      ((-1 : ℝ) ^ n) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n beta hbeta := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [Set.uIcc_of_le hlt.le]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc
        H N hN n beta gamma beta hbeta hlt (left_mem_Icc.mpr hlt.le)
  · rw [Set.uIcc_of_ge hgt.le]
    simpa using
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc
        H N hN n gamma beta beta hgamma hgt (right_mem_Icc.mpr hgt.le)

private theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_uIcc_norm_le
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma t : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hne : beta ≠ gamma) (ht : t ∈ Set.uIcc beta gamma) :
    ‖iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      (Set.uIcc beta gamma) t‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ n := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [Set.uIcc_of_le hlt.le] at ht ⊢
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc_norm_le
        H N hN n beta gamma t hbeta hlt ht
  · rw [Set.uIcc_of_ge hgt.le] at ht ⊢
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_Icc_norm_le
        H N hN n gamma beta t hgamma hgt ht

private theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_taylorWithinEval_uIcc_eq_WilsonTaylorSum
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hne : beta ≠ gamma) :
    taylorWithinEval
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      n (Set.uIcc beta gamma) beta gamma =
      ∑ k ∈ Finset.range (n + 1),
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta gamma k := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_uIcc_at_left
    H N hN k beta gamma hbeta hgamma hne]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
  rfl

/-- Taylor's theorem on the unordered physical coupling interval.  This allows
either ordering of `beta` and `gamma`, while both endpoints remain on the
genuine physical half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le_abs
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN gamma -
        ∑ k ∈ Finset.range (n + 1),
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta gamma k‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ (n + 1) * |gamma - beta| ^ (n + 1) / n.factorial := by
  by_cases hEq : beta = gamma
  · subst gamma
    simpa using
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le
        H N hN n beta beta hbeta le_rfl
  · let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN
    let C :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
    have hC : 0 ≤ C := by
      simpa [C] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
    have hsubset : Set.uIcc beta gamma ⊆ Set.Ici (0 : ℝ) :=
      wilsonCylinderRealAnalyticity_uIcc_subset_Ici beta gamma hbeta hgamma
    have hcont : ContDiffOn ℝ (n + 1 : ℕ) T (Set.uIcc beta gamma) := by
      have hinfty :=
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_contDiffOn_infty
          H N hN
      exact (contDiffOn_infty.1 hinfty (n + 1)).mono hsubset
    have hTaylor := taylor_integral_remainder
      (f := T) (x := gamma) (x₀ := beta) (n := n) hcont
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_taylorWithinEval_uIcc_eq_WilsonTaylorSum
      H N hN n beta gamma hbeta hgamma hEq] at hTaylor
    rw [hTaylor]
    let M : ℝ := C ^ (n + 1) * |gamma - beta| ^ n / n.factorial
    have hInt :
        ‖∫ t in beta..gamma,
            ((gamma - t) ^ n / n.factorial) •
              iteratedDerivWithin (n + 1) T (Set.uIcc beta gamma) t‖ ≤
          M * |gamma - beta| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have htIcc : t ∈ Set.uIcc beta gamma := Set.uIoc_subset_uIcc ht
      have hderiv :
          ‖iteratedDerivWithin (n + 1) T (Set.uIcc beta gamma) t‖ ≤ C ^ (n + 1) := by
        simpa [T, C] using
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin_uIcc_norm_le
            H N hN (n + 1) beta gamma t hbeta hgamma hEq htIcc
      have hdist : |gamma - t| ≤ |gamma - beta| := by
        simpa [Real.dist_eq, abs_sub_comm] using Real.dist_right_le_of_mem_uIcc htIcc
      have hcoeffNonneg : 0 ≤ |gamma - t| ^ n / (n.factorial : ℝ) := by positivity
      have hscalar :
          ‖(gamma - t) ^ n / (n.factorial : ℝ)‖ =
            |gamma - t| ^ n / (n.factorial : ℝ) := by
        simp [Real.norm_eq_abs, abs_div, abs_pow]
      calc
        ‖((gamma - t) ^ n / n.factorial) •
            iteratedDerivWithin (n + 1) T (Set.uIcc beta gamma) t‖ ≤
            ‖(gamma - t) ^ n / (n.factorial : ℝ)‖ *
              ‖iteratedDerivWithin (n + 1) T (Set.uIcc beta gamma) t‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
        _ = (|gamma - t| ^ n / n.factorial) *
              ‖iteratedDerivWithin (n + 1) T (Set.uIcc beta gamma) t‖ := by
          rw [hscalar]
        _ ≤ (|gamma - t| ^ n / n.factorial) * C ^ (n + 1) :=
          mul_le_mul_of_nonneg_left hderiv hcoeffNonneg
        _ ≤ (|gamma - beta| ^ n / n.factorial) * C ^ (n + 1) := by
          have hfrac :
              |gamma - t| ^ n / (n.factorial : ℝ) ≤
                |gamma - beta| ^ n / (n.factorial : ℝ) := by
            gcongr
          exact mul_le_mul_of_nonneg_right hfrac (pow_nonneg hC (n + 1))
        _ = M := by
          dsimp [M]
          ring
    calc
      ‖∫ t in beta..gamma,
          ((gamma - t) ^ n / n.factorial) •
            iteratedDerivWithin (n + 1) T (Set.uIcc beta gamma) t‖ ≤
          M * |gamma - beta| := hInt
      _ = C ^ (n + 1) * |gamma - beta| ^ (n + 1) / n.factorial := by
        dsimp [M]
        rw [pow_succ]
        ring
      _ = _ := by rfl

/-- Absolute exponential majorant for Wilson Taylor terms at arbitrary
physical endpoints. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_norm_le_expMajorant_abs
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (_hgamma : 0 ≤ gamma) (k : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
        H N hN beta hbeta gamma k‖ ≤
      (k.factorial : ℝ)⁻¹ *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N * |gamma - beta|) ^ k := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let d := gamma - beta
  let a : ℝ := (k.factorial : ℝ)⁻¹ * d ^ k
  let s : ℝ := (-1 : ℝ) ^ k
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hInvNonneg : 0 ≤ (k.factorial : ℝ)⁻¹ := by positivity
  have hna : ‖a‖ = (k.factorial : ℝ)⁻¹ * |d| ^ k := by
    dsimp [a]
    simp [abs_mul, abs_pow, hInvNonneg]
  have hns : ‖s‖ = 1 := by
    dsimp [s]
    simp [abs_pow]
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
    _ = ((k.factorial : ℝ)⁻¹ * |d| ^ k) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN k beta hbeta‖ := by
      rw [hna, hns, one_mul]
    _ ≤ ((k.factorial : ℝ)⁻¹ * |d| ^ k) * C ^ k := by
      apply mul_le_mul_of_nonneg_left
      · exact
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_le
            H N hN k beta hbeta
      · exact mul_nonneg hInvNonneg (pow_nonneg (abs_nonneg d) k)
    _ = (k.factorial : ℝ)⁻¹ * (C * |d|) ^ k := by
      rw [mul_pow]
      ring
    _ = _ := by rfl

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_summable_norm_abs
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) :
    Summable (fun k : ℕ =>
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
        H N hN beta hbeta gamma k‖) := by
  let x : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N * |gamma - beta|
  have hmajor : Summable (fun k : ℕ => (k.factorial : ℝ)⁻¹ * x ^ k) := by
    simpa [smul_eq_mul] using
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) x)
  refine Summable.of_nonneg_of_le
    (fun k => ContinuousLinearMap.opNorm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
        H N hN beta hbeta gamma k)) ?_ hmajor
  intro k
  simpa [x] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_norm_le_expMajorant_abs
      H N hN beta gamma hbeta hgamma k

private theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainderMajorantAbs_tendsto_zero
    (H N : ℕ) (beta gamma : ℝ) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N ^ (n + 1) * |gamma - beta| ^ (n + 1) / n.factorial)
      atTop (𝓝 0) := by
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainderMajorant_tendsto_zero
      H N 0 |gamma - beta| (abs_nonneg (gamma - beta))

/-- Two-sided physical-half-line convergence of Wilson Taylor partial sums. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_partialSums_tendsto_transfer_abs
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta gamma k)
      atTop
      (𝓝 (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN gamma)) := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
      H N hN gamma
  let S : ℕ →
      (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) := fun n =>
    ∑ k ∈ Finset.range (n + 1),
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
        H N hN beta hbeta gamma k
  have hdiff : Tendsto (fun n : ℕ => T - S n) atTop (𝓝 0) := by
    refine (ContinuousLinearMap.hasBasis_nhds_zero
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
      (F := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)).tendsto_right_iff.mpr ?_
    rintro ⟨s, U⟩ ⟨hs, hU⟩
    rcases Metric.mem_nhds_iff.1 hU with ⟨epsilon, hepsilon, hballU⟩
    have habs :
        Absorbs ℝ
          (Metric.ball
            (0 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) 1) s :=
      hs (Metric.ball_mem_nhds _ zero_lt_one)
    rcases habs.exists_pos with ⟨M, hM, hMabs⟩
    have hsNorm : ∀ x ∈ s, ‖x‖ < M := by
      intro x hx
      have hxscale :
          x ∈ (M : ℝ) •
            Metric.ball
              (0 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) 1 :=
        hMabs M (by simpa [Real.norm_eq_abs, abs_of_pos hM]) hx
      rcases hxscale with ⟨y, hy, rfl⟩
      have hyNorm : ‖y‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy
      simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hM] using
        (mul_lt_mul_of_pos_left hyNorm hM)
    have hmajor :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainderMajorantAbs_tendsto_zero
        H N beta gamma
    rw [Metric.tendsto_atTop] at hmajor
    rcases hmajor (epsilon / M) (div_pos hepsilon hM) with ⟨N0, hN0⟩
    filter_upwards [eventually_ge_atTop N0] with n hn
    intro x hx
    apply hballU
    have hmajorNonneg :
        0 ≤ periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N ^ (n + 1) * |gamma - beta| ^ (n + 1) / n.factorial := by
      have hC :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
      positivity
    have hmajorLt :
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N ^ (n + 1) * |gamma - beta| ^ (n + 1) / n.factorial <
          epsilon / M := by
      have hdist := hN0 n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hmajorNonneg] at hdist
      exact hdist
    have herr :
        ‖T - S n‖ ≤
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N ^ (n + 1) * |gamma - beta| ^ (n + 1) / n.factorial := by
      simpa [T, S] using
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le_abs
          H N hN n beta gamma hbeta hgamma
    have hpoint : ‖(T - S n) x‖ < epsilon := by
      calc
        ‖(T - S n) x‖ ≤ ‖T - S n‖ * ‖x‖ :=
          (T - S n).le_opNorm x
        _ ≤
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
                H N ^ (n + 1) * |gamma - beta| ^ (n + 1) / n.factorial) * ‖x‖ :=
          mul_le_mul_of_nonneg_right herr (norm_nonneg _)
        _ ≤
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
                H N ^ (n + 1) * |gamma - beta| ^ (n + 1) / n.factorial) * M :=
          mul_le_mul_of_nonneg_left (hsNorm x hx).le hmajorNonneg
        _ < (epsilon / M) * M :=
          mul_lt_mul_of_pos_right hmajorLt hM
        _ = epsilon := by
          field_simp [ne_of_gt hM]
    simpa [Metric.mem_ball, dist_eq_norm] using hpoint
  have hconv :
      Tendsto (fun n : ℕ => T - (T - S n)) atTop (𝓝 (T - 0)) :=
    tendsto_const_nhds.sub hdiff
  have hfun : (fun n : ℕ => T - (T - S n)) = S := by
    funext n
    abel
  have hlim : T - 0 = T := by simp
  rw [hfun, hlim] at hconv
  simpa [T, S] using hconv

/-- Exact Wilson Taylor reconstruction for any two couplings on the physical
half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_hasSum_transfer_abs
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) :
    HasSum
      (fun k : ℕ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta gamma k)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN gamma) := by
  have hnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_summable_norm_abs
      H N hN beta gamma hbeta hgamma
  have hs :
      Tendsto (fun n : ℕ => Finset.range (n + 1)) atTop atTop :=
    tendsto_finset_range.comp (tendsto_add_atTop_nat 1)
  have hpartial :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_partialSums_tendsto_transfer_abs
      H N hN beta gamma hbeta hgamma
  with_reducible_and_instances
    exact hasSum_of_subseq_of_summable
      (f := fun k : ℕ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta gamma k)
      hnorm hs hpartial

private theorem wilsonCylinderRealAnalyticityCoefficient_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) :
    ‖((k.factorial : ℝ)⁻¹) •
        (((-1 : ℝ) ^ k) •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN k beta hbeta)‖ ≤
      (k.factorial : ℝ)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ k := by
  have hInvNonneg : 0 ≤ (k.factorial : ℝ)⁻¹ := by positivity
  have hO :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_norm_le
      H N hN k beta hbeta
  calc
    ‖((k.factorial : ℝ)⁻¹) •
        (((-1 : ℝ) ^ k) •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN k beta hbeta)‖ ≤
      ‖(k.factorial : ℝ)⁻¹‖ *
        ‖((-1 : ℝ) ^ k) •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN k beta hbeta‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖(k.factorial : ℝ)⁻¹‖ *
        (‖(-1 : ℝ) ^ k‖ *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN k beta hbeta‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_smul_le _ _) (norm_nonneg _)
    _ = (k.factorial : ℝ)⁻¹ *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
            H N hN k beta hbeta‖ := by
      simp [Real.norm_eq_abs, hInvNonneg]
    _ ≤ (k.factorial : ℝ)⁻¹ *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N ^ k :=
      mul_le_mul_of_nonneg_left hO hInvNonneg

private theorem formalMultilinearSeries_radius_one_le_of_norm_le_exp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : FormalMultilinearSeries ℝ ℝ F) (C : ℝ)
    (hpNorm : ∀ k : ℕ, ‖p k‖ ≤ (k.factorial : ℝ)⁻¹ * C ^ k) :
    (1 : ℝ≥0∞) ≤ p.radius := by
  have hmajor : Summable (fun k : ℕ => (k.factorial : ℝ)⁻¹ * C ^ k) := by
    simpa [smul_eq_mul] using
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) C)
  have hpSummable : Summable (fun k : ℕ => ‖p k‖ * (1 : ℝ) ^ k) := by
    simp only [one_pow, mul_one]
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg (p k)) hpNorm hmajor
  exact p.le_radius_of_summable (r := (1 : NNReal)) hpSummable

private theorem hasSum_of_norm_remainder_majorant
    {F : Type*} [SeminormedAddCommGroup F]
    (f : ℕ → F) (a : F) (r : ℕ → ℝ)
    (hrNonneg : ∀ n : ℕ, 0 ≤ r n)
    (hrZero : Tendsto r atTop (𝓝 0))
    (hrem : ∀ n : ℕ, ‖a - ∑ k ∈ Finset.range (n + 1), f k‖ ≤ r n)
    (hnorm : Summable (fun k : ℕ => ‖f k‖)) :
    HasSum f a := by
  have hpartial :
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), f k) atTop (𝓝 a) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    have hr := hrZero
    rw [Metric.tendsto_atTop] at hr
    rcases hr epsilon hepsilon with ⟨N0, hN0⟩
    refine ⟨N0, ?_⟩
    intro n hn
    have hrLt : r n < epsilon := by
      have hdist := hN0 n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hrNonneg n)] at hdist
      exact hdist
    calc
      dist (∑ k ∈ Finset.range (n + 1), f k) a =
          ‖a - ∑ k ∈ Finset.range (n + 1), f k‖ := by
        rw [dist_eq_norm, ← norm_neg, neg_sub]
      _ ≤ r n := hrem n
      _ < epsilon := hrLt
  have hs :
      Tendsto (fun n : ℕ => Finset.range (n + 1)) atTop atTop :=
    tendsto_finset_range.comp (tendsto_add_atTop_nat 1)
  exact hasSum_of_subseq_of_summable hnorm hs hpartial

/-- Native Mathlib real analyticity of the Wilson transfer family on the
physical half-line, including `beta = 0`.  The formal multilinear series and
its Wilson reconstruction are both realized in the operator-norm topology. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_analyticWithinAt
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    AnalyticWithinAt ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      (Set.Ici (0 : ℝ)) beta := by
  letI : NormedAddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ
      (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
    ContinuousLinearMap.toNormedSpace
  let C : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let p : FormalMultilinearSeries ℝ ℝ
      (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
    fun k =>
      ContinuousMultilinearMap.mkPiRing ℝ (Fin k)
        (((k.factorial : ℝ)⁻¹) •
          (((-1 : ℝ) ^ k) •
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
              H N hN k beta hbeta))
  have hpNorm : ∀ k : ℕ, ‖p k‖ ≤ (k.factorial : ℝ)⁻¹ * C ^ k := by
    intro k
    dsimp [p]
    rw [ContinuousMultilinearMap.norm_mkPiRing]
    simpa [C] using
      wilsonCylinderRealAnalyticityCoefficient_norm_le H N hN beta hbeta k
  have hradius : (1 : ℝ≥0∞) ≤ p.radius :=
    formalMultilinearSeries_radius_one_le_of_norm_le_exp p C hpNorm
  refine ⟨p, (1 : ℝ≥0∞), ?_⟩
  refine ⟨hradius, zero_lt_one, ?_⟩
  intro y hy _hyBall
  simp only [Set.mem_insert_iff] at hy
  have hgamma : 0 ≤ beta + y := by
    rcases hy with hEq | hmem
    · rw [hEq]
      exact hbeta
    · exact hmem
  let r : ℕ → ℝ := fun n =>
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ (n + 1) * |(beta + y) - beta| ^ (n + 1) / n.factorial
  have hrNonneg : ∀ n : ℕ, 0 ≤ r n := by
    intro n
    have hC :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
    dsimp [r]
    positivity
  have hrZero : Tendsto r atTop (𝓝 0) := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainderMajorantAbs_tendsto_zero
        H N beta (beta + y)
  have hrem : ∀ n : ℕ,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN (beta + y) -
          ∑ k ∈ Finset.range (n + 1),
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
              H N hN beta hbeta (beta + y) k‖ ≤ r n := by
    intro n
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le_abs
        H N hN n beta (beta + y) hbeta hgamma
  have hnorm : Summable (fun k : ℕ =>
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
        H N hN beta hbeta (beta + y) k‖) := by
    simpa using
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_summable_norm_abs
        H N hN beta (beta + y) hbeta hgamma
  have hsum :
      HasSum
        (fun k : ℕ =>
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta (beta + y) k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN (beta + y)) :=
    hasSum_of_norm_remainder_majorant
      (f := fun k : ℕ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta (beta + y) k)
      (a := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN (beta + y))
      (r := r) hrNonneg hrZero hrem hnorm
  have hterm :
      (fun k : ℕ => p k (fun _ : Fin k => y)) =
        (fun k : ℕ =>
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta (beta + y) k) := by
    funext k
    dsimp [p]
    simp [ContinuousMultilinearMap.mkPiRing_apply,
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm,
      smul_smul, mul_assoc, mul_comm, mul_left_comm]
  rw [hterm]
  exact hsum

/-- Public package for the real-analyticity upgrade: the exact two-sided
physical Taylor reconstruction and native within-analyticity are returned
together. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonRealAnalyticity_package
    (H N : ℕ) (hN : 0 < N) :
    (∀ (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma),
      HasSum
        (fun k : ℕ =>
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
            H N hN beta hbeta gamma k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN gamma)) ∧
    (∀ (beta : ℝ) (hbeta : 0 ≤ beta),
      AnalyticWithinAt ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN)
        (Set.Ici (0 : ℝ)) beta) := by
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_hasSum_transfer_abs
      H N hN,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_analyticWithinAt
      H N hN⟩

end
end MathlibAnalytic
end MGAP4D