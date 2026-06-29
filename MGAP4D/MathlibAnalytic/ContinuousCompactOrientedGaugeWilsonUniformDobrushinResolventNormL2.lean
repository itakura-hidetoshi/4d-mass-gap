import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformDobrushinResolventL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pointwise resolvent estimate uniform in the compact Wilson family index. -/
theorem continuous_compact_oriented_uniformResolventL2_norm_bound
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U)
    (y : (U.system i).VacuumOrthogonalL2) :
    ‖U.uniformResolventL2 i hlambda y‖ ≤
      (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ * ‖y‖ := by
  let x : (U.system i).VacuumOrthogonalL2 :=
    U.uniformResolventL2 i hlambda y
  change
    ‖x‖ ≤
      (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ * ‖y‖
  have hShiftPos :
      0 < continuousCompactOrientedUniformDobrushinGap U - lambda :=
    sub_pos.mpr hlambda
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hShiftPos.le) (norm_nonneg y)
  have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hGap :=
    continuous_compact_oriented_uniformDobrushin_restrictedEnergyShift_gap
      U i lambda x
  have hInverse :
      (U.system i).restrictedEnergyShiftL2 lambda x = y := by
    dsimp [x]
    exact continuous_compact_oriented_uniformResolvent_shift_apply
      U i hlambda y
  rw [hInverse] at hGap
  have hCS : inner ℝ y x ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
  have hMul :
      (continuousCompactOrientedUniformDobrushinGap U - lambda) * ‖x‖ ^ 2 ≤
        ‖y‖ * ‖x‖ := hGap.trans hCS
  have hLinear :
      (continuousCompactOrientedUniformDobrushinGap U - lambda) * ‖x‖ ≤ ‖y‖ := by
    nlinarith [sq_nonneg ‖x‖]
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hShiftPos).2
  simpa [mul_comm] using hLinear

/-- Uniform operator-norm bound for all scale-dependent resolvents. -/
theorem continuous_compact_oriented_uniformResolventL2_norm_le
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    (i : ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    ‖U.uniformResolventL2 i hlambda‖ ≤
      (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr (sub_pos.mpr hlambda).le
  · exact continuous_compact_oriented_uniformResolventL2_norm_bound
      U i hlambda

/-- Uniform finite-volume real-gap package for an indexed compact Wilson
family. -/
theorem continuous_compact_oriented_uniformDobrushin_realGap_package
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    ∀ i : ι,
      ∃ R : (U.system i).VacuumOrthogonalL2 →L[ℝ]
          (U.system i).VacuumOrthogonalL2,
        (∀ y, (U.system i).restrictedEnergyShiftL2 lambda (R y) = y) ∧
        (∀ f, R ((U.system i).restrictedEnergyShiftL2 lambda f) = f) ∧
        ‖R‖ ≤
          (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ := by
  intro i
  refine ⟨U.uniformResolventL2 i hlambda, ?_, ?_, ?_⟩
  · exact continuous_compact_oriented_uniformResolvent_shift_apply U i hlambda
  · exact continuous_compact_oriented_uniformResolvent_apply_shift U i hlambda
  · exact continuous_compact_oriented_uniformResolventL2_norm_le U i hlambda

end

end MathlibAnalytic
end MGAP4D
