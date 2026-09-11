import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicNormalizedCenteredRayleighVectorBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- Hamiltonian energies of unit vectors in the Gibbs-vacuum orthogonal sector. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitRayleighEnergySet
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Set ℝ :=
  {r : ℝ |
    ∃ f : Lp ℝ 2 C.gibbsMeasure,
      f ∈ C.VacuumOrthogonalL2 ∧
      ‖f‖ = 1 ∧
      inner ℝ (C.heatBathHamiltonianL2 f) f = r}

/-- The actual finite-volume variational lower edge on the unit
Gibbs-vacuum orthogonal sector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitRayleighInfimum
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : ℝ :=
  sInf C.periodicVacuumOrthogonalUnitRayleighEnergySet

/-- Every energy in the unit vacuum-orthogonal Rayleigh set is nonnegative. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighEnergySet_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {r : ℝ}
    (hr : r ∈ C.periodicVacuumOrthogonalUnitRayleighEnergySet) :
    0 ≤ r := by
  rcases hr with ⟨f, _hfOrth, _hfNorm, rfl⟩
  exact continuous_compact_oriented_heatBathHamiltonianL2_nonneg C f

/-- The unit vacuum-orthogonal Rayleigh energy set is bounded below by zero. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighEnergySet_bddBelow
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    BddBelow C.periodicVacuumOrthogonalUnitRayleighEnergySet := by
  exact ⟨0, fun _r hr =>
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighEnergySet_nonneg
      C hr⟩

/-- A unit vector in the vacuum-orthogonal sector contributes its Hamiltonian
expectation to the Rayleigh energy set. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighEnergySet_mem
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hfOrth : f ∈ C.VacuumOrthogonalL2)
    (hfNorm : ‖f‖ = 1) :
    inner ℝ (C.heatBathHamiltonianL2 f) f ∈
      C.periodicVacuumOrthogonalUnitRayleighEnergySet := by
  exact ⟨f, hfOrth, hfNorm, rfl⟩

/-- If the unit vacuum-orthogonal sector is inhabited, its variational infimum
is nonnegative. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hNonempty : C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty) :
    0 ≤ C.periodicVacuumOrthogonalUnitRayleighInfimum := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitRayleighInfimum
  exact le_csInf hNonempty
    (fun _r hr =>
      continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighEnergySet_nonneg
        C hr)

/-- The variational infimum lies below every realized unit-sector energy. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    {r : ℝ}
    (hr : r ∈ C.periodicVacuumOrthogonalUnitRayleighEnergySet) :
    C.periodicVacuumOrthogonalUnitRayleighInfimum ≤ r := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitRayleighInfimum
  exact csInf_le
    (continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighEnergySet_bddBelow C)
    hr

/-- The actual periodic normalized centered observable contributes its positive
Rayleigh energy to the full vacuum-orthogonal unit-sector energy set. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centeredRayleigh_mem_vacuumOrthogonalUnitRayleighEnergySet :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighEnergySet := by
  refine ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_mem_vacuumOrthogonal,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_norm_eq_one,
    ?_⟩
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_quadratic_eq_rayleigh

/-- Hence the actual finite-volume vacuum-orthogonal unit-sector energy set is
nonempty. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centeredRayleigh_mem_vacuumOrthogonalUnitRayleighEnergySet⟩

/-- The actual finite-volume variational lower edge is nonnegative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighInfimum_nonneg :
    0 ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum := by
  exact
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_nonneg
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty

/-- The concrete positive Rayleigh witness from PR #940 is an explicit upper
bound on the actual finite-volume vacuum-orthogonal variational lower edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighInfimum_le_centeredRayleigh :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF := by
  exact
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_le
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centeredRayleigh_mem_vacuumOrthogonalUnitRayleighEnergySet

/-- Short proof-facing package for the actual finite-volume variational bracket. -/
def periodicHypercubicThreeSpecialUnitaryTwoVacuumOrthogonalRayleighInfimumReceipt : Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty ∧
    BddBelow
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighEnergySet ∧
    0 ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF ∧
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF

/-- The actual side-three periodic `SU(2)` system has a nonempty, zero-bounded
unit vacuum-orthogonal Rayleigh set whose infimum is bracketed above by the
strictly positive concrete centered-observable energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoVacuumOrthogonalRayleighInfimumReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoVacuumOrthogonalRayleighInfimumReceipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty,
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighEnergySet_bddBelow
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighInfimum_nonneg,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighInfimum_le_centeredRayleigh,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centeredRayleigh_pos⟩

end

end MathlibAnalytic
end MGAP4D
