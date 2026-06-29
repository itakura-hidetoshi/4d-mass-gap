import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyShiftGapL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

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
