import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyResolventL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Sharp pointwise resolvent estimate below the restricted Dobrushin gap. -/
theorem continuous_compact_oriented_restrictedEnergyResolventL2_norm_bound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient)
    (y : C.VacuumOrthogonalL2) :
    ‖C.restrictedEnergyResolventL2 D hlambda y‖ ≤
      (continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda)⁻¹ *
        ‖y‖ := by
  let x : C.VacuumOrthogonalL2 :=
    C.restrictedEnergyResolventL2 D hlambda y
  change
    ‖x‖ ≤
      (continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda)⁻¹ *
        ‖y‖
  have hShiftPos :
      0 < continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda :=
    sub_pos.mpr hlambda
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hShiftPos.le) (norm_nonneg y)
  have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hGap :=
    continuous_compact_oriented_restrictedEnergyShiftL2_gap C D lambda x
  have hInverse : C.restrictedEnergyShiftL2 lambda x = y := by
    dsimp [x]
    exact
      continuous_compact_oriented_restrictedEnergyShift_apply_resolvent
        C D hlambda y
  rw [hInverse] at hGap
  have hCS : inner ℝ y x ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
  have hMul :
      (continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda) *
          ‖x‖ ^ 2 ≤
        ‖y‖ * ‖x‖ := hGap.trans hCS
  have hLinear :
      (continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda) *
          ‖x‖ ≤ ‖y‖ := by
    apply (mul_le_mul_right hxNorm).mp
    simpa [pow_two, mul_assoc] using hMul
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hShiftPos).2
  simpa [mul_comm] using hLinear

/-- Operator-norm resolvent bound by the inverse distance to the gap threshold. -/
theorem continuous_compact_oriented_restrictedEnergyResolventL2_norm_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient) :
    ‖C.restrictedEnergyResolventL2 D hlambda‖ ≤
      (continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr (sub_pos.mpr hlambda).le
  · exact
      continuous_compact_oriented_restrictedEnergyResolventL2_norm_bound
        C D hlambda

end

end MathlibAnalytic
end MGAP4D
