import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricTimeTranslation
import MGAP4D.MathlibAnalytic.FiniteWilsonOSFiniteOrderPermutationShiftRigidity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteEvenFourTorusZ2PositiveShiftData

variable
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergyIdentity : 0 ≤ energyIdentity}
    {hEnergyNontrivial : 0 ≤ energyNontrivial}
    {D : FiniteEvenFourTorusWilsonGeometricEnergyData H β energyIdentity
      energyNontrivial hβ hEnergyIdentity hEnergyNontrivial}

/-- The actual even-torus Euclidean-time period is strictly positive. -/
theorem finiteEvenFourTorusTimePeriod_pos :
    0 < finiteEvenFourTorusTimePeriod H := by
  unfold finiteEvenFourTorusTimePeriod
  omega

/-- If the three old permutation-shift obligations are supplied for the actual
one-step even-torus time translation, the completed OS operator is forced to be
the identity. -/
theorem actualGeometricTimeTranslation_hilbertShift_eq_identity
    (S : FiniteEvenFourTorusZ2PositiveShiftData H β energyIdentity
      energyNontrivial hβ hEnergyIdentity hEnergyNontrivial D)
    (hshift : S.shift =
      finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv H) :
    S.toPositiveConfigurationShiftCertificate.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap =
      (finiteEvenFourTorusZ2WilsonOSCertificateOfGeometricEnergyData
        H β energyIdentity energyNontrivial hβ hEnergyIdentity
          hEnergyNontrivial D).oneLayerIdentityTransfer := by
  apply
    S.toPositiveConfigurationShiftCertificate.hilbertShiftContinuousLinearMap_eq_identity_of_shift_pow_eq_refl
      (finiteEvenFourTorusTimePeriod H)
      finiteEvenFourTorusTimePeriod_pos
  change S.shift ^ finiteEvenFourTorusTimePeriod H = Equiv.refl _
  rw [hshift]
  exact
    finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv_pow_period H

/-- At nonzero coupling, no assembled-action witness can coexist with all three
old shift conditions for the actual periodic geometric translation. -/
theorem no_actualGeometricTimeTranslation_action_witness
    (S : FiniteEvenFourTorusZ2PositiveShiftData H β energyIdentity
      energyNontrivial hβ hEnergyIdentity hEnergyNontrivial D)
    (hshift : S.shift =
      finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv H)
    (hBeta : β ≠ 0) :
    ¬ ∃ x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration,
      (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
        hβ hEnergyIdentity hEnergyNontrivial).wilsonAction
          (finiteEvenFourTorusAssemble H (S.shift x) y) ≠
        (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
          hβ hEnergyIdentity hEnergyNontrivial).wilsonAction
          (finiteEvenFourTorusAssemble H x y) := by
  apply
    S.toPositiveConfigurationShiftCertificate.no_wilsonAction_witness_of_finite_order_shift
      (finiteEvenFourTorusTimePeriod H)
      finiteEvenFourTorusTimePeriod_pos
  · change S.shift ^ finiteEvenFourTorusTimePeriod H = Equiv.refl _
    rw [hshift]
    exact
      finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv_pow_period H
  · exact hBeta

/-- Exact incompatibility theorem: a nonzero-coupling Wilson-action witness for
actual one-step time translation rules out any `FiniteEvenFourTorusZ2PositiveShiftData`
realization with that translation.  Thus the three abstract conditions cannot
be discharged nontrivially inside the periodic-permutation interface. -/
theorem no_positiveShiftData_for_actualGeometricTimeTranslation_of_action_witness
    (hBeta : β ≠ 0)
    (x y : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration)
    (hAction :
      (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
        hβ hEnergyIdentity hEnergyNontrivial).wilsonAction
          (finiteEvenFourTorusAssemble H
            (finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv H x) y) ≠
        (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
          hβ hEnergyIdentity hEnergyNontrivial).wilsonAction
          (finiteEvenFourTorusAssemble H x y)) :
    ¬ ∃ S : FiniteEvenFourTorusZ2PositiveShiftData H β energyIdentity
        energyNontrivial hβ hEnergyIdentity hEnergyNontrivial D,
      S.shift = finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv H := by
  rintro ⟨S, hshift⟩
  apply S.no_actualGeometricTimeTranslation_action_witness hshift hBeta
  refine ⟨x, y, ?_⟩
  simpa [hshift] using hAction

/-- Terminal actual-translation classification for the old permutation API. -/
theorem finiteEvenFourTorusActualGeometricTimeTranslationNoGoPackage
    (S : FiniteEvenFourTorusZ2PositiveShiftData H β energyIdentity
      energyNontrivial hβ hEnergyIdentity hEnergyNontrivial D)
    (hshift : S.shift =
      finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv H) :
    S.toPositiveConfigurationShiftCertificate.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap =
        (finiteEvenFourTorusZ2WilsonOSCertificateOfGeometricEnergyData
          H β energyIdentity energyNontrivial hβ hEnergyIdentity
            hEnergyNontrivial D).oneLayerIdentityTransfer ∧
      (β ≠ 0 →
        ¬ ∃ x y :
            (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration,
          (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity
            energyNontrivial hβ hEnergyIdentity hEnergyNontrivial).wilsonAction
              (finiteEvenFourTorusAssemble H (S.shift x) y) ≠
            (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity
              energyNontrivial hβ hEnergyIdentity
                hEnergyNontrivial).wilsonAction
              (finiteEvenFourTorusAssemble H x y)) := by
  exact ⟨S.actualGeometricTimeTranslation_hilbertShift_eq_identity hshift,
    fun hBeta => S.no_actualGeometricTimeTranslation_action_witness
      hshift hBeta⟩

end FiniteEvenFourTorusZ2PositiveShiftData

end

end MathlibAnalytic
end MGAP4D
