import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicRayleighInfimumPoincareOptimalityBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- Arbitrarily small Hamiltonian energies realized by unit vectors in the
Gibbs-vacuum orthogonal sector.  This is the exact approximate-zero-mode
obstruction to strict positivity of the finite-volume Rayleigh infimum. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitApproximateZeroEnergy
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
      ∃ f : Lp ℝ 2 C.gibbsMeasure,
        f ∈ C.VacuumOrthogonalL2 ∧
          ‖f‖ = 1 ∧
            inner ℝ (C.heatBathHamiltonianL2 f) f < ε

/-- For every continuous compact oriented finite-volume system with a nonempty
unit vacuum-orthogonal sector, vanishing of the Rayleigh infimum is equivalent
to the existence of unit vacuum-orthogonal vectors with arbitrarily small
Hamiltonian energy. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_eq_zero_iff_approximateZeroEnergy
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hNonempty :
      C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty) :
    C.periodicVacuumOrthogonalUnitRayleighInfimum = 0 ↔
      C.periodicVacuumOrthogonalUnitApproximateZeroEnergy := by
  constructor
  · intro hInfimumZero ε hεPos
    have hExistsEnergy :
        ∃ r ∈ C.periodicVacuumOrthogonalUnitRayleighEnergySet, r < ε := by
      by_contra hNoEnergy
      push_neg at hNoEnergy
      have hεLeInfimum :
          ε ≤ C.periodicVacuumOrthogonalUnitRayleighInfimum := by
        unfold
          ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitRayleighInfimum
        exact le_csInf hNonempty hNoEnergy
      rw [hInfimumZero] at hεLeInfimum
      exact (not_le_of_gt hεPos) hεLeInfimum
    rcases hExistsEnergy with ⟨r, hrMem, hrLt⟩
    rcases hrMem with ⟨f, hfOrth, hfNorm, rfl⟩
    exact ⟨f, hfOrth, hfNorm, hrLt⟩
  · intro hApproximate
    apply le_antisymm
    · by_contra hInfimumNotLeZero
      have hInfimumPos :
          0 < C.periodicVacuumOrthogonalUnitRayleighInfimum :=
        lt_of_not_ge hInfimumNotLeZero
      rcases hApproximate
          C.periodicVacuumOrthogonalUnitRayleighInfimum hInfimumPos with
        ⟨f, hfOrth, hfNorm, hfEnergyLt⟩
      have hfEnergyMem :
          inner ℝ (C.heatBathHamiltonianL2 f) f ∈
            C.periodicVacuumOrthogonalUnitRayleighEnergySet :=
        continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighEnergySet_mem
          C f hfOrth hfNorm
      have hInfimumLeEnergy :
          C.periodicVacuumOrthogonalUnitRayleighInfimum ≤
            inner ℝ (C.heatBathHamiltonianL2 f) f :=
        continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_le
          C hfEnergyMem
      exact (not_lt_of_ge hInfimumLeEnergy) hfEnergyLt
    · exact
        continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_nonneg
          C hNonempty

/-- Strict positivity of the finite-volume Rayleigh infimum is equivalent to
absence of approximate zero-energy unit vectors.  This is a characterization,
not a proof that either side holds. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_pos_iff_not_approximateZeroEnergy
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hNonempty :
      C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty) :
    0 < C.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      ¬ C.periodicVacuumOrthogonalUnitApproximateZeroEnergy := by
  have hNonneg :
      0 ≤ C.periodicVacuumOrthogonalUnitRayleighInfimum :=
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_nonneg
      C hNonempty
  constructor
  · intro hInfimumPos hApproximate
    have hInfimumZero :
        C.periodicVacuumOrthogonalUnitRayleighInfimum = 0 :=
      (continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_eq_zero_iff_approximateZeroEnergy
        C hNonempty).2 hApproximate
    rw [hInfimumZero] at hInfimumPos
    exact lt_irrefl 0 hInfimumPos
  · intro hNoApproximate
    have hInfimumNeZero :
        C.periodicVacuumOrthogonalUnitRayleighInfimum ≠ 0 := by
      intro hInfimumZero
      exact hNoApproximate
        ((continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_eq_zero_iff_approximateZeroEnergy
          C hNonempty).1 hInfimumZero)
    exact lt_of_le_of_ne hNonneg (Ne.symm hInfimumNeZero)

/-- The actual side-three periodic `SU(2)` Rayleigh infimum vanishes exactly
when actual unit Gibbs-vacuum orthogonal vectors realize arbitrarily small
heat-bath Hamiltonian energies. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_eq_zero_iff_approximateZeroEnergy :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum = 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateZeroEnergy := by
  exact
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_eq_zero_iff_approximateZeroEnergy
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty

/-- Thus the remaining actual positive-Poincare frontier is exactly exclusion
of actual approximate zero-energy vectors.  No positive lower bound is asserted. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_not_approximateZeroEnergy :
    0 <
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateZeroEnergy := by
  exact
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_pos_iff_not_approximateZeroEnergy
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty

/-- Compact proof-facing package for the exact actual approximate-zero-mode
frontier. -/
def periodicHypercubicThreeSpecialUnitaryTwoRayleighApproximateZeroFrontierReceipt : Prop :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum = 0 ↔
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateZeroEnergy) ∧
  (0 <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
    ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateZeroEnergy) ∧
  0 ≤
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ∧
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ≤
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF ∧
  0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF

/-- The actual finite-volume lower edge is nonnegative and bounded above by the
known positive observable-specific Rayleigh energy.  Its vanishing is exactly
approximate-zero-mode existence, while its positivity is exactly their
exclusion.  This does not establish a spectral gap, a volume-uniform bound, a
continuum limit, or the Yang--Mills mass gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoRayleighApproximateZeroFrontierReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoRayleighApproximateZeroFrontierReceipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_eq_zero_iff_approximateZeroEnergy,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_not_approximateZeroEnergy,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighInfimum_nonneg,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighInfimum_le_centeredRayleigh,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centeredRayleigh_pos⟩

end

end MathlibAnalytic
end MGAP4D
