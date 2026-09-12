import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyEquivalenceL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The bounded inverse of the native heat-bath energy operator on the
Gibbs-vacuum orthogonal sector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.restrictedEnergyInverseL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 :=
  (C.restrictedEnergyEquivalenceL2 D).symm.toContinuousLinearMap

/-- The restricted energy operator is a left inverse of its bounded inverse. -/
theorem continuous_compact_oriented_restrictedEnergy_apply_inverse
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (y : C.VacuumOrthogonalL2) :
    C.heatBathHamiltonianVacuumOrthogonalL2 (C.restrictedEnergyInverseL2 D y) = y := by
  change
    C.heatBathHamiltonianVacuumOrthogonalL2
        ((C.restrictedEnergyEquivalenceL2 D).symm y) = y
  rw [← continuous_compact_oriented_restrictedEnergyEquivalenceL2_apply]
  exact (C.restrictedEnergyEquivalenceL2 D).apply_symm_apply y

/-- The bounded inverse is a left inverse of the restricted energy operator. -/
theorem continuous_compact_oriented_restrictedEnergy_inverse_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : C.VacuumOrthogonalL2) :
    C.restrictedEnergyInverseL2 D
        (C.heatBathHamiltonianVacuumOrthogonalL2 f) = f := by
  change
    (C.restrictedEnergyEquivalenceL2 D).symm
        (C.heatBathHamiltonianVacuumOrthogonalL2 f) = f
  rw [← continuous_compact_oriented_restrictedEnergyEquivalenceL2_apply]
  exact (C.restrictedEnergyEquivalenceL2 D).symm_apply_apply f

end

end MathlibAnalytic
end MGAP4D
