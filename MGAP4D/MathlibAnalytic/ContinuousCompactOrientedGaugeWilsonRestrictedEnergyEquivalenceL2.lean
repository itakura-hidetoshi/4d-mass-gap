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

end

end MathlibAnalytic
end MGAP4D
