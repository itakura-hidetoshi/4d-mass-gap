import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRestrictedEnergyResolventNormL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every real shift below the Dobrushin gap is bijective on the excitation
Hilbert sector. -/
theorem continuous_compact_oriented_restrictedEnergyShiftL2_bijective
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient) :
    Function.Bijective (C.restrictedEnergyShiftL2 lambda) := by
  constructor
  · intro f g hfg
    calc
      f = C.restrictedEnergyResolventL2 D hlambda
          (C.restrictedEnergyShiftL2 lambda f) :=
        (continuous_compact_oriented_restrictedEnergyResolvent_apply_shift
          C D hlambda f).symm
      _ = C.restrictedEnergyResolventL2 D hlambda
          (C.restrictedEnergyShiftL2 lambda g) := by rw [hfg]
      _ = g :=
        continuous_compact_oriented_restrictedEnergyResolvent_apply_shift
          C D hlambda g
  · intro y
    exact
      ⟨C.restrictedEnergyResolventL2 D hlambda y,
        continuous_compact_oriented_restrictedEnergyShift_apply_resolvent
          C D hlambda y⟩

/-- Real resolvent package expressing the complete finite-volume gap interval
below the Dobrushin threshold. -/
theorem continuous_compact_oriented_restrictedEnergy_realGap_package
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate C)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedDobrushinHeatBathGap D.coefficient) :
    ∃ R : C.VacuumOrthogonalL2 →L[ℝ] C.VacuumOrthogonalL2,
      (∀ y, C.restrictedEnergyShiftL2 lambda (R y) = y) ∧
      (∀ f, R (C.restrictedEnergyShiftL2 lambda f) = f) ∧
      ‖R‖ ≤
        (continuousCompactOrientedDobrushinHeatBathGap D.coefficient - lambda)⁻¹ := by
  refine ⟨C.restrictedEnergyResolventL2 D hlambda, ?_, ?_, ?_⟩
  · exact continuous_compact_oriented_restrictedEnergyShift_apply_resolvent C D hlambda
  · exact continuous_compact_oriented_restrictedEnergyResolvent_apply_shift C D hlambda
  · exact continuous_compact_oriented_restrictedEnergyResolventL2_norm_le C D hlambda

end

end MathlibAnalytic
end MGAP4D
