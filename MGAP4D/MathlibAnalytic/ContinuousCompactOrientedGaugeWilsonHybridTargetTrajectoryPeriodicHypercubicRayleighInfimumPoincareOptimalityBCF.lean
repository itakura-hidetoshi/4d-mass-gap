import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicVacuumOrthogonalRayleighInfimumBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- Vacuum centering commutes with the finite-volume heat-bath Hamiltonian
because the Hamiltonian annihilates the normalized Gibbs vacuum. -/
theorem continuous_compact_oriented_periodicRayleighInfimumPoincare_heatBathHamiltonian_vacuumCentered
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 (C.vacuumCenteredL2 f) =
      C.heatBathHamiltonianL2 f := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [map_sub, map_smul,
    continuous_compact_oriented_heatBathHamiltonianL2_vacuum]
  simp

/-- Vacuum centering preserves the heat-bath Hamiltonian quadratic form. -/
theorem continuous_compact_oriented_periodicRayleighInfimumPoincare_vacuumCentered_quadratic_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ
        (C.heatBathHamiltonianL2 (C.vacuumCenteredL2 f))
        (C.vacuumCenteredL2 f) =
      inner ℝ (C.heatBathHamiltonianL2 f) f := by
  rw [continuous_compact_oriented_periodicRayleighInfimumPoincare_heatBathHamiltonian_vacuumCentered]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [inner_sub_right, real_inner_smul_right]
  have hVacuumPairing :
      inner ℝ (C.heatBathHamiltonianL2 f) C.gibbsVacuumL2 = 0 := by
    calc
      inner ℝ (C.heatBathHamiltonianL2 f) C.gibbsVacuumL2 =
          inner ℝ f (C.heatBathHamiltonianL2 C.gibbsVacuumL2) :=
        continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
          C f C.gibbsVacuumL2
      _ = 0 := by
        rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
          inner_zero_right]
  rw [hVacuumPairing]
  ring

/-- The heat-bath Hamiltonian quadratic form scales quadratically under real
scalar multiplication. -/
theorem continuous_compact_oriented_periodicRayleighInfimumPoincare_quadratic_smul
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (a : ℝ)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 (a • f)) (a • f) =
      a ^ 2 * inner ℝ (C.heatBathHamiltonianL2 f) f := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Every nonzero Gibbs `L²` vector normalizes to norm one. -/
theorem continuous_compact_oriented_periodicRayleighInfimumPoincare_normalize_norm_eq_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hf : f ≠ 0) :
    ‖‖f‖⁻¹ • f‖ = 1 := by
  have hNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hNormPos)]
  exact inv_mul_cancel₀ (ne_of_gt hNormPos)

/-- Vacuum centering lands in the Gibbs-vacuum orthogonal sector. -/
theorem continuous_compact_oriented_periodicRayleighInfimumPoincare_vacuumCentered_mem_orthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.vacuumCenteredL2 f ∈ C.VacuumOrthogonalL2 := by
  apply
    (continuous_compact_oriented_mem_vacuumOrthogonalL2_iff
      C (C.vacuumCenteredL2 f)).2
  exact
    continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_vacuumCentered_inner_zero
      C f

/-- On every system with an inhabited unit vacuum-orthogonal sector, the
variational infimum itself is a valid finite-volume heat-bath Poincare
constant.  Its value may still be zero. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_heatBathPoincare
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hNonempty :
      C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty) :
    C.HeatBathPoincareL2
      C.periodicVacuumOrthogonalUnitRayleighInfimum := by
  intro f
  let centered := C.vacuumCenteredL2 f
  change
    C.periodicVacuumOrthogonalUnitRayleighInfimum * ‖centered‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f
  by_cases hCentered : centered = 0
  · simpa [hCentered] using
      (continuous_compact_oriented_heatBathHamiltonianL2_nonneg C f)
  · let normalized := ‖centered‖⁻¹ • centered
    have hNormPos : 0 < ‖centered‖ := norm_pos_iff.mpr hCentered
    have hNormNe : ‖centered‖ ≠ 0 := ne_of_gt hNormPos
    have hCenteredOrth : centered ∈ C.VacuumOrthogonalL2 := by
      simpa [centered] using
        (continuous_compact_oriented_periodicRayleighInfimumPoincare_vacuumCentered_mem_orthogonal
          C f)
    have hNormalizedOrth : normalized ∈ C.VacuumOrthogonalL2 := by
      exact C.VacuumOrthogonalL2.smul_mem _ hCenteredOrth
    have hNormalizedNorm : ‖normalized‖ = 1 := by
      simpa [normalized] using
        (continuous_compact_oriented_periodicRayleighInfimumPoincare_normalize_norm_eq_one
          C centered hCentered)
    have hNormalizedEnergyMem :
        inner ℝ (C.heatBathHamiltonianL2 normalized) normalized ∈
          C.periodicVacuumOrthogonalUnitRayleighEnergySet := by
      exact
        continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighEnergySet_mem
          C normalized hNormalizedOrth hNormalizedNorm
    have hInfimumLe :
        C.periodicVacuumOrthogonalUnitRayleighInfimum ≤
          inner ℝ (C.heatBathHamiltonianL2 normalized) normalized :=
      continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_le
        C hNormalizedEnergyMem
    have hRecover : ‖centered‖ • normalized = centered := by
      dsimp [normalized]
      rw [smul_smul, mul_inv_cancel₀ hNormNe, one_smul]
    have hScale :
        inner ℝ (C.heatBathHamiltonianL2 centered) centered =
          ‖centered‖ ^ 2 *
            inner ℝ (C.heatBathHamiltonianL2 normalized) normalized := by
      have hScaleRaw :=
        continuous_compact_oriented_periodicRayleighInfimumPoincare_quadratic_smul
          C ‖centered‖ normalized
      rw [hRecover] at hScaleRaw
      exact hScaleRaw
    have hCenteredEnergy :
        inner ℝ (C.heatBathHamiltonianL2 centered) centered =
          inner ℝ (C.heatBathHamiltonianL2 f) f := by
      simpa [centered] using
        (continuous_compact_oriented_periodicRayleighInfimumPoincare_vacuumCentered_quadratic_eq
          C f)
    calc
      C.periodicVacuumOrthogonalUnitRayleighInfimum * ‖centered‖ ^ 2 =
          ‖centered‖ ^ 2 *
            C.periodicVacuumOrthogonalUnitRayleighInfimum := by ring
      _ ≤ ‖centered‖ ^ 2 *
          inner ℝ (C.heatBathHamiltonianL2 normalized) normalized :=
        mul_le_mul_of_nonneg_left hInfimumLe (sq_nonneg ‖centered‖)
      _ = inner ℝ (C.heatBathHamiltonianL2 centered) centered := hScale.symm
      _ = inner ℝ (C.heatBathHamiltonianL2 f) f := hCenteredEnergy

/-- Every heat-bath Poincare constant is bounded above by the unit-sector
variational infimum. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_maximal_poincare
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hNonempty :
      C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty)
    (hPoincare : C.HeatBathPoincareL2 gap) :
    gap ≤ C.periodicVacuumOrthogonalUnitRayleighInfimum := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitRayleighInfimum
  apply le_csInf hNonempty
  intro r hr
  rcases hr with ⟨f, hfOrth, hfNorm, rfl⟩
  have hfInner : inner ℝ C.gibbsVacuumL2 f = 0 :=
    (continuous_compact_oriented_mem_vacuumOrthogonalL2_iff C f).1 hfOrth
  have hCentered : C.vacuumCenteredL2 f = f :=
    continuous_compact_oriented_vacuumCenteredL2_eq_self C f hfInner
  simpa [hCentered, hfNorm] using hPoincare f

/-- The variational lower edge is exactly the largest admissible heat-bath
Poincare constant. -/
theorem continuous_compact_oriented_gap_le_periodicVacuumOrthogonalUnitRayleighInfimum_iff_poincare
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hNonempty :
      C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty)
    (gap : ℝ) :
    gap ≤ C.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      C.HeatBathPoincareL2 gap := by
  constructor
  · intro hGapLe
    intro f
    have hInfimumPoincare :=
      continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_heatBathPoincare
        C hNonempty f
    have hScaleLe := mul_le_mul_of_nonneg_right hGapLe
      (sq_nonneg ‖C.vacuumCenteredL2 f‖)
    exact le_trans hScaleLe hInfimumPoincare
  · intro hPoincare
    exact
      continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_maximal_poincare
        C gap hNonempty hPoincare

/-- Strict positivity of the variational lower edge is equivalent to existence
of some strictly positive heat-bath Poincare constant.  This theorem is a
characterization, not a proof of either side. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_pos_iff_exists_positive_poincare
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hNonempty :
      C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty) :
    0 < C.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      ∃ gap : ℝ, 0 < gap ∧ C.HeatBathPoincareL2 gap := by
  constructor
  · intro hInfimumPos
    exact ⟨
      C.periodicVacuumOrthogonalUnitRayleighInfimum,
      hInfimumPos,
      continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_heatBathPoincare
        C hNonempty⟩
  · rintro ⟨gap, hGapPos, hPoincare⟩
    exact lt_of_lt_of_le hGapPos
      (continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_maximal_poincare
        C gap hNonempty hPoincare)

/-- The actual side-three periodic `SU(2)` variational infimum is a valid
finite-volume heat-bath Poincare constant.  Its positivity is not asserted. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_heatBathPoincare :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum := by
  exact
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_heatBathPoincare
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty

/-- Any actual finite-volume heat-bath Poincare constant is no larger than the
actual unit-sector variational infimum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_poincare_le_rayleighInfimum
    (gap : ℝ)
    (hPoincare :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 gap) :
    gap ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum := by
  exact
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_maximal_poincare
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      gap
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty
      hPoincare

/-- Actual constants below the variational lower edge are exactly the valid
finite-volume heat-bath Poincare constants. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_gap_le_rayleighInfimum_iff_poincare
    (gap : ℝ) :
    gap ≤
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 gap := by
  exact
    continuous_compact_oriented_gap_le_periodicVacuumOrthogonalUnitRayleighInfimum_iff_poincare
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty
      gap

/-- Positivity of the actual variational lower edge is exactly the remaining
positive-Poincare problem.  Neither side is proved here. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_exists_positive_poincare :
    0 <
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      ∃ gap : ℝ,
        0 < gap ∧
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 gap := by
  exact
    continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_pos_iff_exists_positive_poincare
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty

/-- Compact proof-facing package for actual finite-volume Poincare optimality. -/
def periodicHypercubicThreeSpecialUnitaryTwoRayleighInfimumPoincareOptimalityReceipt : Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ∧
    (∀ gap : ℝ,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 gap →
        gap ≤
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum) ∧
    (∀ gap : ℝ,
      gap ≤
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 gap) ∧
    (0 <
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      ∃ gap : ℝ,
        0 < gap ∧
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 gap) ∧
    0 ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF

/-- The actual variational infimum is a nonnegative maximal heat-bath Poincare
constant, remains bounded above by the concrete positive centered-observable
Rayleigh energy, and is positive exactly when some positive Poincare constant
exists. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoRayleighInfimumPoincareOptimalityReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoRayleighInfimumPoincareOptimalityReceipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_heatBathPoincare,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_poincare_le_rayleighInfimum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_gap_le_rayleighInfimum_iff_poincare,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_exists_positive_poincare,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighInfimum_nonneg,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighInfimum_le_centeredRayleigh⟩

end

end MathlibAnalytic
end MGAP4D
