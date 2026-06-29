import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyInverseNormL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Real spectral shift of the restricted native heat-bath energy operator. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.restrictedEnergyShiftL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (lambda : ℝ) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 :=
  C.heatBathHamiltonianVacuumOrthogonalL2 -
    lambda • ContinuousLinearMap.id ℝ C.VacuumOrthogonalL2

@[simp] theorem continuous_compact_oriented_restrictedEnergyShiftL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (lambda : ℝ)
    (f : C.VacuumOrthogonalL2) :
    C.restrictedEnergyShiftL2 lambda f =
      C.heatBathHamiltonianVacuumOrthogonalL2 f - lambda • f := by
  rfl

/-- Bounded bilinear form associated with the real spectral shift. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.restrictedEnergyShiftFormL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (lambda : ℝ) :
    C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2 →L[ℝ] ℝ :=
  (innerSL ℝ).comp (C.restrictedEnergyShiftL2 lambda)

@[simp] theorem continuous_compact_oriented_restrictedEnergyShiftFormL2_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (lambda : ℝ)
    (f g : C.VacuumOrthogonalL2) :
    C.restrictedEnergyShiftFormL2 lambda f g =
      inner ℝ (C.restrictedEnergyShiftL2 lambda f) g :=
  rfl

end

end MathlibAnalytic
end MGAP4D
