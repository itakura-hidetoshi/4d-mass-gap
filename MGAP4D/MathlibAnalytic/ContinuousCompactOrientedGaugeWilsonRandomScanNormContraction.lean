import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanOperator

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Pointwise uniform-norm estimate for the exact compact random-scan
heat-bath sweep. -/
theorem continuous_compact_oriented_randomScanHeatBathSweep_abs_le_norm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |C.randomScanHeatBathSweep O A| ≤ ‖O‖ := by
  let n : ℝ := Fintype.card C.base.geometry.Edge
  have hn : 0 < n := by
    exact_mod_cast hEdge
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hinv : 0 ≤ n⁻¹ := inv_nonneg.mpr hn.le
  unfold ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweep
  change
    |n⁻¹ * ∑ target : C.base.geometry.Edge,
      C.singleLinkHeatBathProjection target O A| ≤ ‖O‖
  rw [abs_mul, abs_of_nonneg hinv]
  calc
    n⁻¹ * |∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathProjection target O A| ≤
      n⁻¹ * ∑ target : C.base.geometry.Edge,
        |C.singleLinkHeatBathProjection target O A| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs Finset.univ
          (fun target : C.base.geometry.Edge =>
            C.singleLinkHeatBathProjection target O A)) hinv
    _ ≤ n⁻¹ * ∑ _target : C.base.geometry.Edge, ‖O‖ := by
      apply mul_le_mul_of_nonneg_left _ hinv
      apply Finset.sum_le_sum
      intro target _htarget
      exact
        continuous_compact_oriented_singleLinkHeatBathProjection_abs_le_norm
          C target O A
    _ = ‖O‖ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      change n⁻¹ * (n * ‖O‖) = ‖O‖
      field_simp [hn0]

/-- The exact compact random-scan heat-bath sweep contracts the uniform norm. -/
theorem continuous_compact_oriented_randomScanHeatBathSweepBCF_norm_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    ‖C.randomScanHeatBathSweepBCF O‖ ≤ ‖O‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg O)).2
  intro A
  simpa [Real.norm_eq_abs] using
    continuous_compact_oriented_randomScanHeatBathSweep_abs_le_norm
      C hEdge O A

/-- The operator norm of the exact compact random-scan heat-bath map is at
most one. -/
theorem continuous_compact_oriented_randomScanHeatBathContinuousLinearMap_norm_le_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    ‖C.randomScanHeatBathContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (by norm_num)
  intro O
  simpa using
    continuous_compact_oriented_randomScanHeatBathSweepBCF_norm_le
      C hEdge O

end
end MathlibAnalytic
end MGAP4D
