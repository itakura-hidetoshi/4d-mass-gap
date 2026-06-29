import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyLaxMilgramL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.restrictedEnergyEquivalenceL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C) :
    C.VacuumOrthogonalL2 ≃L[ℝ] C.VacuumOrthogonalL2 :=
  (continuous_compact_oriented_restrictedEnergyFormL2_isCoercive C D).continuousLinearEquivOfBilin

/-- The Lax--Milgram equivalence acts by the restricted energy operator. -/
theorem continuous_compact_oriented_restrictedEnergyEquivalenceL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    (f : C.VacuumOrthogonalL2) :
    C.restrictedEnergyEquivalenceL2 D f =
      C.heatBathHamiltonianVacuumOrthogonalL2 f := by
  change
    InnerProductSpace.continuousLinearMapOfBilin C.restrictedEnergyFormL2 f =
      C.heatBathHamiltonianVacuumOrthogonalL2 f
  symm
  apply InnerProductSpace.unique_continuousLinearMapOfBilin
  intro g
  rfl

end

end MathlibAnalytic
end MGAP4D
