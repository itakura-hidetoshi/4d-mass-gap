import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderTaylorDifferentialCore
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology ContDiff BigOperators Pointwise

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

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
        ext v
        simp [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm, hb0]
      · simp
    rw [hsum, sub_self, ContinuousLinearMap.opNorm_zero]
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
      exact (contDiffOn_infty.1 hinfty (n + 1)).mono hsubset
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
  refine Summable.of_nonneg_of_le
    (fun k => ContinuousLinearMap.opNorm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
        H N hN beta hbeta gamma k)) ?_ hmajor
  intro k
  simpa [x] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylorTerm_norm_le_expMajorant
      H N hN beta gamma hbeta hbg k

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

end
end MathlibAnalytic
end MGAP4D