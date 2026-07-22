import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonContinuousLinearEquivL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Generic range reconstruction: if an ambient continuous linear endomorphism
lands in a submodule and its internal restriction is surjective, then its ambient
linear range is exactly that submodule. -/
theorem continuousLinearMap_range_eq_submodule_of_internal_surjective
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (A : E →L[𝕜] E)
    (S : Submodule 𝕜 E)
    (B : S →L[𝕜] S)
    (hA_mem : ∀ x : E, A x ∈ S)
    (hB_apply : ∀ x : S, ((B x : S) : E) = A (x : E))
    (hB_surjective : Function.Surjective B) :
    A.toLinearMap.range = S := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact hA_mem x
  · intro y hy
    let yS : S := ⟨y, hy⟩
    rcases hB_surjective yS with ⟨x, hx⟩
    refine ⟨(x : E), ?_⟩
    calc
      A.toLinearMap (x : E) = (B x : E) := (hB_apply x).symm
      _ = y := by
        exact congrArg Subtype.val hx

/-- Generic solvability criterion extracted from an exact range identification. -/
theorem continuousLinearMap_exists_apply_eq_iff_mem_submodule_of_range_eq
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    (A : E →L[𝕜] E)
    (S : Submodule 𝕜 E)
    (hRange : A.toLinearMap.range = S)
    (f : E) :
    (∃ u : E, A u = f) ↔ f ∈ S := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [← hRange]
    exact ⟨u, rfl⟩
  · intro hf
    rw [← hRange] at hf
    rcases hf with ⟨u, hu⟩
    exact ⟨u, hu⟩

/-- The ambient beta-zero Poisson range is exactly the Gibbs-vacuum orthogonal
submodule. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_range_eq_vacuumOrthogonalSubmoduleL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 := by
  apply continuousLinearMap_range_eq_submodule_of_internal_surjective
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_mem_vacuumOrthogonalSubmoduleL2
        f
  · intro f
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply
        f
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreen_rightInverse_poissonVacuumOrthogonalEndL2.surjective

/-- Finite-volume beta-zero Fredholm alternative: the ambient Poisson equation
is solvable exactly for Gibbs-vacuum orthogonal data. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_randomScanPoissonOperatorL2_apply_eq_iff_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    (∃ u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f) ↔
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 := by
  have hSolvability :=
    continuousLinearMap_exists_apply_eq_iff_mem_submodule_of_range_eq
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_range_eq_vacuumOrthogonalSubmoduleL2
      f
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff]
    at hSolvability
  exact hSolvability

/-- Every vacuum-orthogonal datum has a unique vacuum-orthogonal Poisson
solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_randomScanPoissonVacuumOrthogonalEndL2_solution
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ∃! u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u = f := by
  refine ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      f,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self
      f,
    ?_⟩
  intro u hu
  apply
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_injective
  exact hu.trans
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self
      f).symm

/-- The canonical vacuum-orthogonal solution obeys the sharp inverse-norm
estimate with factor `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_le_324_mul_norm
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        f‖ ≤
      324 * ‖f‖ := by
  have hFundamental :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2.le_opNorm
      f
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_eq_324]
    at hFundamental
  exact hFundamental

/-- Every vacuum-orthogonal ambient solution satisfies the same `324` a priori
bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_le_324_mul_norm_of_inner_vacuum_eq_zero_of_randomScanPoissonOperatorL2_apply_eq
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          u = 0)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f) :
    ‖u‖ ≤ 324 * ‖f‖ := by
  have hBound :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_le_324_mul_norm_randomScanPoissonOperatorL2_apply_of_inner_vacuum_eq_zero
      u hOrthogonal
  rw [hPoisson] at hBound
  exact hBound

/-- For vacuum-orthogonal data, all ambient solutions are the exact Green
solution plus an arbitrary cardinality-zero Gibbs-vacuum component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_iff_exists_green_add_vacuumProjector_of_inner_vacuum_eq_zero
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        u = f ↔
      ∃ w : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
              f +
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 w := by
  have hVacuumZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f = 0 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
      hOrthogonal, zero_smul]
  simpa [hVacuumZero] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredPoisson_solution_iff_exists_vacuumProjector
      f u

/-- Compact receipt for the finite-volume beta-zero Poisson Fredholm
alternative. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFredholmAlternativeL2Receipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 ∧
    (∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      (∃ u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u = f) ↔
        inner ℝ
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
            f = 0) ∧
    (∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      ∃! u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            u = f) ∧
    (∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f‖ ≤
        324 * ‖f‖)

/-- The finite-volume beta-zero Poisson Fredholm-alternative receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFredholmAlternativeL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFredholmAlternativeL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_range_eq_vacuumOrthogonalSubmoduleL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_randomScanPoissonOperatorL2_apply_eq_iff_inner_vacuum_eq_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_randomScanPoissonVacuumOrthogonalEndL2_solution,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_le_324_mul_norm⟩

end

end MathlibAnalytic
end MGAP4D
