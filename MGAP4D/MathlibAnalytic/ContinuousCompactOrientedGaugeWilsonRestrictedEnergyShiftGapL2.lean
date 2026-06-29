import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyShiftL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem continuous_compact_oriented_restrictedEnergyShiftL2_gap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (lambda : ℝ)
    (f : C.VacuumOrthogonalL2) :
    (continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda) *
        ‖f‖ ^ 2 ≤
      inner ℝ (C.restrictedEnergyShiftL2 lambda f) f := by
  have hGap := continuous_compact_oriented_restrictedEnergy_gap C D f
  rw [continuous_compact_oriented_restrictedEnergyShiftL2_apply]
  have hInner :
      inner ℝ
          (C.heatBathHamiltonianVacuumOrthogonalL2 f - lambda • f) f =
        inner ℝ (C.heatBathHamiltonianVacuumOrthogonalL2 f) f -
          lambda * ‖f‖ ^ 2 := by
    calc
      inner ℝ
          (C.heatBathHamiltonianVacuumOrthogonalL2 f - lambda • f) f =
        inner ℝ (C.heatBathHamiltonianVacuumOrthogonalL2 f) f -
          inner ℝ (lambda • f) f := inner_sub_left _ _ _
      _ = inner ℝ (C.heatBathHamiltonianVacuumOrthogonalL2 f) f -
          lambda * ‖f‖ ^ 2 := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hInner]
  nlinarith [sq_nonneg ‖f‖]

end

end MathlibAnalytic
end MGAP4D
