import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderTaylorRemainder
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology ContDiff BigOperators Pointwise

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

local instance wilsonCylinderTaylorSeriesConvergencePhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

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
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainderMajorant_tendsto_zero
        H N beta gamma hbg
    rw [Metric.tendsto_atTop] at hmajor
    rcases hmajor (epsilon / M) (div_pos hepsilon hM) with ⟨N0, hN0⟩
    filter_upwards [eventually_ge_atTop N0] with n hn
    intro x hx
    apply hballU
    have hmajorNonneg :
        0 ≤ periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N ^ (n + 1) * (gamma - beta) ^ (n + 1) / n.factorial := by
      have hC :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
      have hd : 0 ≤ gamma - beta := sub_nonneg.mpr hbg
      positivity
    have hmajorLt :
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N ^ (n + 1) * (gamma - beta) ^ (n + 1) / n.factorial <
          epsilon / M := by
      have hdist := hN0 n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hmajorNonneg] at hdist
      exact hdist
    have herr :
        ‖T - S n‖ ≤
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N ^ (n + 1) * (gamma - beta) ^ (n + 1) / n.factorial := by
      simpa [T, S] using
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le
          H N hN n beta gamma hbeta hbg
    have hpoint : ‖(T - S n) x‖ < epsilon := by
      calc
        ‖(T - S n) x‖ ≤ ‖T - S n‖ * ‖x‖ :=
          (T - S n).le_opNorm x
        _ ≤
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
                H N ^ (n + 1) * (gamma - beta) ^ (n + 1) / n.factorial) * ‖x‖ :=
          mul_le_mul_of_nonneg_right herr (norm_nonneg _)
        _ ≤
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
                H N ^ (n + 1) * (gamma - beta) ^ (n + 1) / n.factorial) * M :=
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
  with_reducible_and_instances
    exact hasSum_of_subseq_of_summable
      (f := fun k : ℕ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta gamma k)
      hnorm hs hpartial

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