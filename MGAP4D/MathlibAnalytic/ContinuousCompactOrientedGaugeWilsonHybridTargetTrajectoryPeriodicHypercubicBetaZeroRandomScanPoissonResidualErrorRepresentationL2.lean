import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonGreenVariationalPrincipleL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The residual of a continuous linear equation `A u = b`. -/
def continuousLinearMapResidual
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (b u : E) : E :=
  b - A u

/-- An exact solution identifies the residual with the operator applied to the
solution error. -/
theorem continuousLinearMap_residual_eq_apply_solution_sub
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (b uStar u : E)
    (hSolution : A uStar = b) :
    continuousLinearMapResidual A b u = A (uStar - u) := by
  unfold continuousLinearMapResidual
  rw [map_sub, hSolution]

/-- A bounded inverse recovery of the residual gives an a posteriori norm bound
for the solution error. -/
theorem continuousLinearMap_norm_solution_sub_le_opNorm_mul_norm_residual
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A G : E →L[ℝ] E)
    (b uStar u : E)
    (hInverseResidual :
      G (continuousLinearMapResidual A b u) = uStar - u) :
    ‖uStar - u‖ ≤
      ‖G‖ * ‖continuousLinearMapResidual A b u‖ := by
  rw [← hInverseResidual]
  exact G.le_opNorm (continuousLinearMapResidual A b u)

/-- The quadratic form of a continuous linear map is bounded above by its
operator norm times the squared ambient norm. -/
theorem continuousLinearMap_inner_apply_self_le_opNorm_mul_norm_sq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (x : E) :
    inner ℝ (T x) x ≤ ‖T‖ * ‖x‖ ^ 2 := by
  have hInner :
      inner ℝ (T x) x ≤ ‖T x‖ * ‖x‖ :=
    le_trans (le_abs_self _)
      (abs_real_inner_le_norm (T x) x)
  have hNorm : ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
    T.le_opNorm x
  have hScaled :
      ‖T x‖ * ‖x‖ ≤ (‖T‖ * ‖x‖) * ‖x‖ :=
    mul_le_mul_of_nonneg_right hNorm (norm_nonneg x)
  nlinarith [ContinuousLinearMap.opNorm_nonneg T, norm_nonneg x]

/-- If a compatible inverse recovers the residual as the solution error, then
the Dirichlet energy gap is exactly one half of the inverse-residual quadratic
form. -/
theorem continuousLinearMap_dirichletEnergy_sub_solution_eq_half_inverseResidual_quadraticForm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A G : E →L[ℝ] E)
    (b uStar u : E)
    (hA : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hSolution : A uStar = b)
    (hInverseResidual :
      G (continuousLinearMapResidual A b u) = uStar - u) :
    continuousLinearMapDirichletEnergy A b u -
        continuousLinearMapDirichletEnergy A b uStar =
      ((1 : ℝ) / 2) *
        inner ℝ
          (G (continuousLinearMapResidual A b u))
          (continuousLinearMapResidual A b u) := by
  rw [continuousLinearMap_dirichletEnergy_sub_solution_eq_quadraticGap
    A b uStar hA hSolution u]
  rw [hInverseResidual,
    continuousLinearMap_residual_eq_apply_solution_sub A b uStar u hSolution]
  have hNeg : u - uStar = -(uStar - u) := by
    abel
  calc
    ((1 : ℝ) / 2) * inner ℝ (A (u - uStar)) (u - uStar) =
        ((1 : ℝ) / 2) *
          inner ℝ (A (uStar - u)) (uStar - u) := by
            rw [hNeg, map_neg, inner_neg_left, inner_neg_right]
            ring
    _ = ((1 : ℝ) / 2) *
          inner ℝ (uStar - u) (A (uStar - u)) := by
            rw [hA (uStar - u) (uStar - u)]

/-- Residual vanishing is equivalent to equality with the exact solution when
the inverse recovers the residual error. -/
theorem continuousLinearMap_residual_eq_zero_iff_eq_solution
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A G : E →L[ℝ] E)
    (b uStar u : E)
    (hSolution : A uStar = b)
    (hInverseResidual :
      G (continuousLinearMapResidual A b u) = uStar - u) :
    continuousLinearMapResidual A b u = 0 ↔ u = uStar := by
  constructor
  · intro hResidual
    have hRecovered := hInverseResidual
    rw [hResidual, map_zero] at hRecovered
    exact (sub_eq_zero.mp hRecovered.symm).symm
  · intro hEq
    rw [hEq]
    unfold continuousLinearMapResidual
    rw [hSolution, sub_self]

/-- The actual centered Poisson residual `C f - A u` on `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  continuousLinearMapResidual
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
    (u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)

/-- The ambient error between the Moore--Penrose solution and any centered
competitor remains Gibbs-vacuum orthogonal. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_generalizedInverse_sub_subtype_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) = 0 := by
  have hGeneralizedInverse :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)).1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_mem_vacuumOrthogonalSubmoduleL2
        f)
  have hu :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
      u.property
  rw [inner_sub_right, hGeneralizedInverse, hu, sub_self]

/-- The actual centered residual is the Poisson image of the ambient solution
error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_poisson_apply_generalizedInverse_sub
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
    continuousLinearMapResidual
  rw [map_sub,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2]

/-- Applying the generalized inverse to the residual exactly recovers the
ambient solution error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_residual_eq_generalizedInverse_sub
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f -
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_poisson_apply_generalizedInverse_sub,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_poisson_eq_sub_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_generalizedInverse_sub_subtype_eq_zero,
    zero_smul, sub_zero]

/-- Every actual centered residual is Gibbs-vacuum orthogonal. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonResidualL2_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u) = 0 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_poisson_apply_generalizedInverse_sub]
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)))).1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_mem_vacuumOrthogonalSubmoduleL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)))

/-- The residual is exactly solved by its generalized-inverse image. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_residual_eq_self
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u)) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_self_of_inner_vacuum_eq_zero
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonResidualL2_eq_zero
        f u)

/-- The residual vanishes exactly at the canonical centered solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_zero_iff_eq_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u = 0 ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f := by
  constructor
  · intro hResidual
    have hRecovered :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_residual_eq_generalizedInverse_sub
        f u
    rw [hResidual, map_zero] at hRecovered
    apply Subtype.ext
    calc
      (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f :=
        (sub_eq_zero.mp hRecovered.symm).symm
      _ =
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply
          f
  · intro hCanonical
    rw [hCanonical,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_poisson_apply_generalizedInverse_sub]
    have hCoe :
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply
        f).symm
    rw [hCoe, sub_self, map_zero]

/-- The ambient solution error is controlled by the residual with the exact
generalized-inverse factor `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_sub_subtype_le_324_mul_norm_residual
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f -
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ≤
      324 *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ := by
  have hBound :=
    continuousLinearMap_norm_solution_sub_le_opNorm_mul_norm_residual
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_residual_eq_generalizedInverse_sub
        f u)
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonGeneralizedInverseL2_eq_324] using
    hBound

/-- The actual Dirichlet energy gap is exactly one half of the generalized
inverse quadratic form of the residual. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_half_generalizedInverse_residual_quadraticForm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) =
      ((1 : ℝ) / 2) *
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
              f u))
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u) := by
  have hGeneric :=
    continuousLinearMap_dirichletEnergy_sub_solution_eq_half_inverseResidual_quadraticForm
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_inner_symm
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2
        f)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_residual_eq_generalizedInverse_sub
        f u)
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2,
    continuousLinearMapDirichletEnergy,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply] using
    hGeneric

/-- The Green-functional maximum gap is exactly the generalized-inverse
quadratic form of the residual. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_eq_generalizedInverse_residual_quadraticForm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u =
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u))
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_neg_two_mul_dirichletEnergy,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_neg_two_mul_dirichletEnergy,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_half_generalizedInverse_residual_quadraticForm]
  ring

/-- The generalized-inverse residual quadratic form is bounded above by
`324 ‖r‖²`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_residual_quadraticForm_le_324_mul_norm_sq
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u))
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u) ≤
      324 *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ^ 2 := by
  have hUpper :=
    continuousLinearMap_inner_apply_self_le_opNorm_mul_norm_sq
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u)
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonGeneralizedInverseL2_eq_324] using
    hUpper

/-- The Dirichlet energy gap admits the residual-only a posteriori upper bound
`162 ‖r‖²`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_le_162_mul_norm_residual_sq
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ≤
      162 *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ^ 2 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_half_generalizedInverse_residual_quadraticForm]
  have hUpper :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_residual_quadraticForm_le_324_mul_norm_sq
      f u
  nlinarith

/-- The Green-functional maximum gap admits the residual-only upper bound
`324 ‖r‖²`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_le_324_mul_norm_residual_sq
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u ≤
      324 *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ^ 2 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_eq_generalizedInverse_residual_quadraticForm]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_residual_quadraticForm_le_324_mul_norm_sq
      f u

/-- The residual-to-error stability factor `324` is attained by a nonzero
cardinality-one mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_vacuumOrthogonal_norm_error_eq_324_mul_norm_residual :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ =
        324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_inner_vacuum_eq_zero_randomScanPoissonOperatorL2_apply_eq_inv_324_smul
    with ⟨w, hwNe, hwOrthogonal, hPoisson⟩
  let u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨w,
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        w).2 hwOrthogonal⟩
  refine ⟨u, ?_, ?_⟩
  · intro hu
    apply hwNe
    have hCoe := congrArg
      (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (z : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hu
    simpa only [u] using hCoe
  · change
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          w‖ =
        324 *
          ‖continuousLinearMapResidual
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2
              (0 : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
            w‖
    unfold continuousLinearMapResidual
    rw [map_zero, map_zero, hPoisson]
    simp only [zero_sub, norm_neg, norm_smul]
    norm_num

/-- Structured receipt for the actual beta-zero residual error representation
and a posteriori variational bounds. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualErrorRepresentationL2Receipt :
    Prop where
  residual_is_poisson_error :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f -
            (u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
  inverse_residual_is_error :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  residual_zero_iff_canonical :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u = 0 ↔
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f
  error_norm_bound :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ≤
        324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖
  dirichlet_gap_residual :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) =
        ((1 : ℝ) / 2) *
          inner ℝ
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
                f u))
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
              f u)
  green_gap_residual :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f u =
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
              f u))
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u)
  residual_energy_upper :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) ≤
        162 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ^ 2
  sharp_error_factor :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ =
        324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u‖

/-- The actual finite-volume side-three periodic `SU(2)`, beta-zero random-scan
system satisfies the complete residual error representation receipt. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualErrorRepresentationL2_receipt :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualErrorRepresentationL2Receipt := by
  exact
    { residual_is_poisson_error :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_poisson_apply_generalizedInverse_sub
      inverse_residual_is_error :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_residual_eq_generalizedInverse_sub
      residual_zero_iff_canonical :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_zero_iff_eq_canonical
      error_norm_bound :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_sub_subtype_le_324_mul_norm_residual
      dirichlet_gap_residual :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_half_generalizedInverse_residual_quadraticForm
      green_gap_residual :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_eq_generalizedInverse_residual_quadraticForm
      residual_energy_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_le_162_mul_norm_residual_sq
      sharp_error_factor :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_vacuumOrthogonal_norm_error_eq_324_mul_norm_residual }

end

end MathlibAnalytic
end MGAP4D
