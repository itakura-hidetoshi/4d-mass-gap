import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyShiftCoerciveL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Lax--Milgram equivalence for a real shift below the Dobrushin gap. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.restrictedEnergyShiftEquivalenceL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient) :
    C.VacuumOrthogonalL2 ≃L[ℝ] C.VacuumOrthogonalL2 :=
  (continuous_compact_oriented_restrictedEnergyShiftFormL2_isCoercive
    C D hlambda).continuousLinearEquivOfBilin

/-- The shifted Lax--Milgram equivalence acts by `H - lambda I`. -/
theorem continuous_compact_oriented_restrictedEnergyShiftEquivalenceL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient)
    (f : C.VacuumOrthogonalL2) :
    C.restrictedEnergyShiftEquivalenceL2 D hlambda f =
      C.restrictedEnergyShiftL2 lambda f := by
  change
    InnerProductSpace.continuousLinearMapOfBilin
        (C.restrictedEnergyShiftFormL2 lambda) f =
      C.restrictedEnergyShiftL2 lambda f
  symm
  apply InnerProductSpace.unique_continuousLinearMapOfBilin
  intro g
  rfl

/-- Continuous real resolvent of the restricted energy operator below the gap. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.restrictedEnergyResolventL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 :=
  (C.restrictedEnergyShiftEquivalenceL2 D hlambda).symm.toContinuousLinearMap

/-- The shifted energy operator followed by its resolvent is the identity. -/
theorem continuous_compact_oriented_restrictedEnergyShift_apply_resolvent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient)
    (y : C.VacuumOrthogonalL2) :
    C.restrictedEnergyShiftL2 lambda
        (C.restrictedEnergyResolventL2 D hlambda y) = y := by
  change
    C.restrictedEnergyShiftL2 lambda
        ((C.restrictedEnergyShiftEquivalenceL2 D hlambda).symm y) = y
  rw [← continuous_compact_oriented_restrictedEnergyShiftEquivalenceL2_apply]
  exact (C.restrictedEnergyShiftEquivalenceL2 D hlambda).apply_symm_apply y

/-- The resolvent followed by the shifted energy operator is the identity. -/
theorem continuous_compact_oriented_restrictedEnergyResolvent_apply_shift
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient)
    (f : C.VacuumOrthogonalL2) :
    C.restrictedEnergyResolventL2 D hlambda
        (C.restrictedEnergyShiftL2 lambda f) = f := by
  change
    (C.restrictedEnergyShiftEquivalenceL2 D hlambda).symm
        (C.restrictedEnergyShiftL2 lambda f) = f
  rw [← continuous_compact_oriented_restrictedEnergyShiftEquivalenceL2_apply]
  exact (C.restrictedEnergyShiftEquivalenceL2 D hlambda).symm_apply_apply f

end

end MathlibAnalytic
end MGAP4D
