import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyShiftL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Below the Dobrushin gap, every real shift remains strictly coercive. -/
theorem continuous_compact_oriented_restrictedEnergyShiftL2_gap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (lambda : ℝ)
    (f : C.VacuumOrthogonalL2) :
    (continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda) *
        ‖f‖ ^ 2 ≤
      inner ℝ (C.restrictedEnergyShiftL2 lambda f) f := by
  have hGap := continuous_compact_oriented_restrictedEnergy_gap C D f
  rw [continuous_compact_oriented_restrictedEnergyShiftL2_apply,
    inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖f‖]

/-- The shifted restricted energy form is coercive below the Dobrushin gap. -/
theorem continuous_compact_oriented_restrictedEnergyShiftFormL2_isCoercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient) :
    IsCoercive (C.restrictedEnergyShiftFormL2 lambda) := by
  refine
    ⟨continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda,
      sub_pos.mpr hlambda, ?_⟩
  intro f
  change
    (continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda) *
        ‖f‖ * ‖f‖ ≤
      inner ℝ (C.restrictedEnergyShiftL2 lambda f) f
  simpa [pow_two, mul_assoc] using
    continuous_compact_oriented_restrictedEnergyShiftL2_gap C D lambda f

end

end MathlibAnalytic
end MGAP4D
