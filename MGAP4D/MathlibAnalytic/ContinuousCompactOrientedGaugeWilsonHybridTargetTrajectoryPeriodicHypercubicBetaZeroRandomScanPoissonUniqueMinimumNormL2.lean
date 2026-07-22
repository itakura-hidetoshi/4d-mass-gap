import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonGeneralizedInverseL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Generic equality case of Pythagoras: for orthogonal vectors, adding the
right summand preserves the norm exactly iff that summand vanishes. -/
theorem norm_add_eq_norm_left_iff_of_inner_eq_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (x y : E)
    (hxy : inner ℝ x y = 0) :
    ‖x + y‖ = ‖x‖ ↔ y = 0 := by
  constructor
  · intro hNorm
    have hPythagoras :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y hxy
    rw [hNorm] at hPythagoras
    have hyNorm : ‖y‖ = 0 := by
      nlinarith [norm_nonneg x, norm_nonneg y]
    exact norm_eq_zero.mp hyNorm
  · intro hy
    rw [hy, add_zero]

/-- The ambient generalized inverse is Gibbs-vacuum orthogonal. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonGeneralizedInverseL2_apply_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) = 0 := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)).1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_mem_vacuumOrthogonalSubmoduleL2
        f)

/-- The canonical generalized-inverse solution is orthogonal to every
cardinality-zero Gibbs-vacuum component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_randomScanPoissonGeneralizedInverseL2_apply_fluctuationCardinalityProjectorL2_zero_apply_eq_zero
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 u) = 0 := by
  have hOrthogonal :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonGeneralizedInverseL2_apply_eq_zero
      f
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum]
  simp [real_inner_comm, hOrthogonal]

/-- Every ambient Poisson solution is the canonical generalized-inverse
solution plus its exact cardinality-zero Gibbs-vacuum component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_add_fluctuationCardinalityProjectorL2_zero_apply_of_randomScanPoissonOperatorL2_apply_eq
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f) :
    u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 u := by
  have hCentered :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector
      u
  rw [hPoisson] at hCentered
  calc
    u =
      (u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 u) +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 u := by
      abel
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 u := by
      rw [← hCentered]

/-- Exact Pythagorean norm identity for every ambient beta-zero Poisson
solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_randomScanPoisson_solution_eq_norm_sq_generalizedInverse_add_norm_sq_vacuumProjector
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f) :
    ‖u‖ * ‖u‖ =
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ +
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 u‖ *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 u‖ := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_add_fluctuationCardinalityProjectorL2_zero_apply_of_randomScanPoissonOperatorL2_apply_eq
    f u hPoisson]
  exact
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 u)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_randomScanPoissonGeneralizedInverseL2_apply_fluctuationCardinalityProjectorL2_zero_apply_eq_zero
        f u)

/-- Equality in the minimum-norm bound occurs exactly when the solution has no
Gibbs-vacuum component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_eq_norm_generalizedInverse_iff_vacuumProjector_eq_zero_of_randomScanPoissonOperatorL2_apply_eq
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f) :
    ‖u‖ =
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 u = 0 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_add_fluctuationCardinalityProjectorL2_zero_apply_of_randomScanPoissonOperatorL2_apply_eq
    f u hPoisson]
  exact
    norm_add_eq_norm_left_iff_of_inner_eq_zero
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 u)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_randomScanPoissonGeneralizedInverseL2_apply_fluctuationCardinalityProjectorL2_zero_apply_eq_zero
        f u)

/-- Any Poisson solution whose norm is no larger than the canonical solution is
itself the canonical generalized-inverse solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_of_randomScanPoissonOperatorL2_apply_eq_of_norm_le
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f)
    (hNorm :
      ‖u‖ ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖) :
    u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f := by
  have hMinimum :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_randomScanPoissonOperatorL2_apply_eq
      f u hPoisson
  have hNormEq :
      ‖u‖ =
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ :=
    le_antisymm hNorm hMinimum
  have hVacuumZero :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_eq_norm_generalizedInverse_iff_vacuumProjector_eq_zero_of_randomScanPoissonOperatorL2_apply_eq
      f u hPoisson).1 hNormEq
  have hDecomposition :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_add_fluctuationCardinalityProjectorL2_zero_apply_of_randomScanPoissonOperatorL2_apply_eq
      f u hPoisson
  rw [hVacuumZero, add_zero] at hDecomposition
  exact hDecomposition

/-- Among solutions of the same Poisson equation, equality with the minimum
norm is equivalent to equality with the generalized-inverse solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_eq_norm_generalizedInverse_iff_eq_generalizedInverse_of_randomScanPoissonOperatorL2_apply_eq
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f) :
    ‖u‖ =
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f := by
  constructor
  · intro hNorm
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_of_randomScanPoissonOperatorL2_apply_eq_of_norm_le
        f u hPoisson hNorm.le
  · intro hu
    rw [hu]

/-- Every noncanonical ambient solution has strictly larger norm than the
canonical generalized-inverse solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_lt_norm_of_randomScanPoissonOperatorL2_apply_eq_of_ne
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f)
    (hNe :
      u ≠
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f‖ < ‖u‖ := by
  have hMinimum :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_randomScanPoissonOperatorL2_apply_eq
      f u hPoisson
  have hNormNe :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f‖ ≠ ‖u‖ := by
    intro hEq
    apply hNe
    exact
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_eq_norm_generalizedInverse_iff_eq_generalizedInverse_of_randomScanPoissonOperatorL2_apply_eq
        f u hPoisson).1 hEq.symm
  exact lt_of_le_of_ne hMinimum hNormNe

/-- Every Gibbs-vacuum orthogonal datum has a unique minimum-norm ambient
Poisson solution, namely the generalized-inverse solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_minimumNorm_randomScanPoisson_solution_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ∃! u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          u = f ∧
        ∀ v : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              v = f →
            ‖u‖ ≤ ‖v‖ := by
  let g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
      f
  have hGPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          g = f := by
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_self_of_inner_vacuum_eq_zero
        f hOrthogonal
  refine ⟨g, ?_, ?_⟩
  · refine ⟨hGPoisson, ?_⟩
    intro v hv
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_le_norm_of_randomScanPoissonOperatorL2_apply_eq
        f v hv
  · intro u hu
    have hNorm : ‖u‖ ≤ ‖g‖ := hu.2 g hGPoisson
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_of_randomScanPoissonOperatorL2_apply_eq_of_norm_le
        f u hu.1 hNorm

/-- Structured receipt for exact orthogonal decomposition and unique
minimum-norm beta-zero Poisson solvability. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonUniqueMinimumNormL2Receipt :
    Prop where
  solution_decomposition :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u = f →
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 f +
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 0 u
  pythagorean_identity :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u = f →
        ‖u‖ * ‖u‖ =
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 f‖ *
              ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 f‖ +
            ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 0 u‖ *
              ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 0 u‖
  equality_iff_canonical :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u = f →
        (‖u‖ =
            ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 f‖ ↔
          u = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 f)
  strict_off_canonical :
    ∀ f u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u = f →
        u ≠ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 f →
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2 f‖ < ‖u‖
  unique_minimum_solution :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      inner ℝ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f = 0 →
        ∃! u : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u = f ∧
            ∀ v : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 v = f →
                ‖u‖ ≤ ‖v‖

/-- The unique-minimum-norm Poisson receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonUniqueMinimumNormL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonUniqueMinimumNormL2Receipt := by
  refine
    { solution_decomposition := ?_
      pythagorean_identity := ?_
      equality_iff_canonical := ?_
      strict_off_canonical := ?_
      unique_minimum_solution := ?_ }
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_eq_randomScanPoissonGeneralizedInverseL2_apply_add_fluctuationCardinalityProjectorL2_zero_apply_of_randomScanPoissonOperatorL2_apply_eq
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sq_randomScanPoisson_solution_eq_norm_sq_generalizedInverse_add_norm_sq_vacuumProjector
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_eq_norm_generalizedInverse_iff_eq_generalizedInverse_of_randomScanPoissonOperatorL2_apply_eq
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_lt_norm_of_randomScanPoissonOperatorL2_apply_eq_of_ne
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_minimumNorm_randomScanPoisson_solution_of_inner_vacuum_eq_zero

end

end MathlibAnalytic
end MGAP4D
