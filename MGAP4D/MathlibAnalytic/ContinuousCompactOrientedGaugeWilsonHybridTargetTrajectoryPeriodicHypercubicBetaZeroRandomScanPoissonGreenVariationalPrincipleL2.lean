import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonDirichletPrincipleL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The concave Green variational functional associated with a continuous
linear endomorphism and a right-hand side on a real inner-product space. -/
def continuousLinearMapGreenVariationalFunctional
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (b u : E) : ℝ :=
  2 * inner ℝ b u - inner ℝ (A u) u

/-- The Green variational functional is exactly minus twice the Dirichlet
energy. -/
theorem continuousLinearMap_greenVariationalFunctional_eq_neg_two_mul_dirichletEnergy
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (b u : E) :
    continuousLinearMapGreenVariationalFunctional A b u =
      -2 * continuousLinearMapDirichletEnergy A b u := by
  unfold continuousLinearMapGreenVariationalFunctional
    continuousLinearMapDirichletEnergy
  ring

/-- For an inner-symmetric operator, every exact solution gives the exact
quadratic maximum gap of the Green variational functional. -/
theorem continuousLinearMap_greenVariationalFunctional_solution_sub_eq_quadraticGap
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (b uStar : E)
    (hA : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hSolution : A uStar = b)
    (u : E) :
    continuousLinearMapGreenVariationalFunctional A b uStar -
        continuousLinearMapGreenVariationalFunctional A b u =
      inner ℝ (A (u - uStar)) (u - uStar) := by
  unfold continuousLinearMapGreenVariationalFunctional
  rw [← hSolution]
  simp only [map_sub, inner_sub_left, inner_sub_right]
  rw [hA u uStar, real_inner_comm u (A uStar)]
  ring

/-- The actual beta-zero Green variational functional on the Gibbs-vacuum
orthogonal sector. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : ℝ :=
  2 * inner ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
    inner ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)

/-- The actual Green functional is minus twice the actual Dirichlet energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_neg_two_mul_dirichletEnergy
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
        f u =
      -2 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
  ring

/-- Exact Green-functional maximum-gap identity on the actual beta-zero
Gibbs-vacuum orthogonal sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_eq_quadraticGap
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
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          ((u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)))
        ((u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) := by
  have hGap :=
    continuousLinearMap_greenVariationalFunctional_solution_sub_eq_quadraticGap
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_inner_symm
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2
        f)
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2,
    continuousLinearMapGreenVariationalFunctional,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply] using
    hGap

/-- The Green-functional maximum gap controls squared distance to the canonical
centered solution with the sharp coefficient `1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_sub_canonical_le_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 324) *
        ‖(u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_eq_quadraticGap]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonOperatorL2_quadraticForm_of_inner_vacuum_eq_zero
      ((u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_sub_randomScanCanonicalPoissonSolution_eq_zero
        f u)

/-- The canonical Green-functional value is the Moore--Penrose quadratic form. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_eq_generalizedInverse_quadraticForm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f) =
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f := by
  let g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
      f
  have hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          g =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
    simpa only [g] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2
        f
  have hCenter :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 g = g := by
    simpa only [g] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_generalizedInverse_eq_self
        f
  have hCenteredInner :
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
          g =
        inner ℝ g f := by
    calc
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
          g =
        inner ℝ f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 g) :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_inner_symm
          f g
      _ = inner ℝ f g := by rw [hCenter]
      _ = inner ℝ g f := real_inner_comm f g
  have hValue :
      2 * inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
          g -
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            g)
          g =
      inner ℝ g f := by
    rw [hPoisson, hCenteredInner]
    ring
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2,
    g,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply] using
    hValue

/-- The canonical centered solution globally maximizes the Green variational
functional on `Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_le_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
        f u ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f) := by
  have hStrong :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_sub_canonical_le_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub
      f u
  have hNonneg :
      0 ≤ ((1 : ℝ) / 324) *
        ‖(u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 := by
    positivity
  linarith

/-- Every centered competitor is bounded above by the Moore--Penrose quadratic
form. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_le_generalizedInverse_quadraticForm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
        f u ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
        f u ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_le_canonical
        f u
    _ = inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_eq_generalizedInverse_quadraticForm
        f

/-- Equality with the maximum Green-functional value occurs exactly at the
canonical centered solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_canonical_iff_eq_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f := by
  constructor
  · intro hFunctional
    have hStrong :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_sub_canonical_le_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub
        f u
    rw [hFunctional, sub_self] at hStrong
    have hNorm :
        ‖(u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ = 0 := by
      nlinarith [norm_nonneg
        ((u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))]
    apply Subtype.ext
    exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)
  · rintro rfl
    rfl

/-- Equality with the Moore--Penrose quadratic-form upper bound occurs exactly
at the canonical centered solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_generalizedInverse_quadraticForm_iff_eq_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u =
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)
          f ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f := by
  rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_eq_generalizedInverse_quadraticForm]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_canonical_iff_eq_canonical
      f u

/-- Maximizing the Green functional is equivalent to solving the centered
Poisson equation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_canonical_iff_poisson_eq_centering
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_canonical_iff_eq_canonical
      f u).trans
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_centering_iff_eq_canonical
        f u).symm

/-- Maximizing the Green functional is equivalent to the Dirichlet
Euler--Lagrange condition. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_canonical_iff_eulerLagrange
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystemBetaZeroRandomScanPoissonDirichletEulerLagrangeL2
        f u := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_canonical_iff_eq_canonical
      f u).trans
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEulerLagrangeL2_iff_eq_canonical
        f u).symm

/-- The Moore--Penrose quadratic form is the greatest attained value of the
actual Green variational functional. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_isGreatest_generalizedInverse_quadraticForm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsGreatest
      (Set.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f))
      (inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f)
        f) := by
  constructor
  · refine ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
      f, ?_⟩
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_eq_generalizedInverse_quadraticForm
        f
  · intro y hy
    rcases hy with ⟨u, rfl⟩
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_le_generalizedInverse_quadraticForm
        f u

/-- The canonical Dirichlet minimum is minus one half of the Moore--Penrose
quadratic form. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_canonical_eq_neg_half_generalizedInverse_quadraticForm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f) =
      -((1 : ℝ) / 2) *
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)
          f := by
  have hRelation :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_neg_two_mul_dirichletEnergy
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        f)
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_eq_generalizedInverse_quadraticForm]
    at hRelation
  linarith

/-- The primal Dirichlet minimum and dual Green maximum have zero duality gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletGreen_zero_duality_gap
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) +
        ((1 : ℝ) / 2) *
          inner ℝ
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f)
            f = 0 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_canonical_eq_neg_half_generalizedInverse_quadraticForm]
  ring

/-- The maximum-gap coefficient `1 / 324` is attained at zero datum by a
nonzero cardinality-one centered mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonGreenVariationalFunctionalL2_zero_maxGap_eq_inv_324_mul_norm_sq :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u =
        ((1 : ℝ) / 324) *
          ‖(u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_inner_vacuum_eq_zero_randomScanPoissonOperatorL2_quadraticForm_eq_inv_324_mul_norm_sq
    with ⟨x, hxNe, hxOrthogonal, hxQuadratic⟩
  let u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨x,
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        x).2 hxOrthogonal⟩
  have huNe : u ≠ 0 := by
    intro hu
    apply hxNe
    have hCoe := congrArg
      (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (z : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hu
    simpa only [u] using hCoe
  have hCanonicalZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          (0 : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
    exact map_zero
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
  have hGap :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_eq_quadraticGap
      (0 : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      u
  rw [hCanonicalZero] at hGap
  simp only [sub_zero] at hGap
  refine ⟨u, huNe, ?_⟩
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          (0 : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          0 -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          (0 : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          u =
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          x)
        x := by
      simpa only [u] using hGap
    _ = ((1 : ℝ) / 324) * ‖x‖ ^ 2 := hxQuadratic
    _ = ((1 : ℝ) / 324) *
        ‖(u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 := by
      rfl

/-- Structured receipt for the actual beta-zero Poisson Green variational
principle on the Gibbs-vacuum orthogonal sector. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalPrincipleL2Receipt :
    Prop where
  exact_maximum_gap :
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
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            ((u : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
                f : Lp ℝ 2
                  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)))
          ((u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
  sharp_maximum_gap_lower :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ((1 : ℝ) / 324) *
          ‖(u : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f u
  canonical_value :
    ∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) =
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)
          f
  unique_maximizer :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) ↔
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f
  greatest_value :
    ∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsGreatest
        (Set.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f))
        (inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f)
          f)
  zero_duality_gap :
    ∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) +
          ((1 : ℝ) / 2) *
            inner ℝ
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
                f)
              f = 0

/-- The actual finite-volume side-three periodic `SU(2)`, beta-zero random-scan
system satisfies the full Poisson Green variational receipt. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalPrincipleL2_receipt :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalPrincipleL2Receipt := by
  exact
    { exact_maximum_gap :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_eq_quadraticGap
      sharp_maximum_gap_lower :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_sub_canonical_le_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub
      canonical_value :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_eq_generalizedInverse_quadraticForm
      unique_maximizer :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_canonical_iff_eq_canonical
      greatest_value :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_isGreatest_generalizedInverse_quadraticForm
      zero_duality_gap :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletGreen_zero_duality_gap }

end
end MathlibAnalytic
end MGAP4D
