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

/-- The restricted energy operator is bijective. -/
theorem continuous_compact_oriented_restrictedEnergy_bijective
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C) :
    Function.Bijective C.heatBathHamiltonianVacuumOrthogonalL2 := by
  constructor
  · intro f g hfg
    apply (C.restrictedEnergyEquivalenceL2 D).injective
    simpa only [continuous_compact_oriented_restrictedEnergyEquivalenceL2_apply] using hfg
  · intro y
    refine ⟨(C.restrictedEnergyEquivalenceL2 D).symm y, ?_⟩
    rw [← continuous_compact_oriented_restrictedEnergyEquivalenceL2_apply]
    exact (C.restrictedEnergyEquivalenceL2 D).apply_symm_apply y

end

end MathlibAnalytic
end MGAP4D
