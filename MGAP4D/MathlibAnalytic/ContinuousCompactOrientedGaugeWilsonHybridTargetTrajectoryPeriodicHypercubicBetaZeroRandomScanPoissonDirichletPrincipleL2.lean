import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonMoorePenrosePositiveL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The Dirichlet energy associated with a continuous linear endomorphism and a
right-hand side on a real inner-product space. -/
def continuousLinearMapDirichletEnergy
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (b u : E) : ℝ :=
  ((1 : ℝ) / 2) * inner ℝ (A u) u - inner ℝ b u

/-- For an inner-symmetric operator, every exact solution gives the exact
quadratic Dirichlet energy gap. -/
theorem continuousLinearMap_dirichletEnergy_sub_solution_eq_quadraticGap
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (b uStar : E)
    (hA : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hSolution : A uStar = b)
    (u : E) :
    continuousLinearMapDirichletEnergy A b u -
        continuousLinearMapDirichletEnergy A b uStar =
      ((1 : ℝ) / 2) * inner ℝ (A (u - uStar)) (u - uStar) := by
  unfold continuousLinearMapDirichletEnergy
  rw [← hSolution]
  simp only [map_sub, inner_sub_left, inner_sub_right]
  rw [hA u uStar, real_inner_comm u (A uStar)]
  ring

/-- The actual beta-zero Dirichlet energy on the Gibbs-vacuum orthogonal
subspace, with right-hand side equal to ambient orthogonal centering. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : ℝ :=
  ((1 : ℝ) / 2) *
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
    inner ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)

/-- The difference between an arbitrary centered competitor and the canonical
centered solution remains Gibbs-vacuum orthogonal. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_sub_randomScanCanonicalPoissonSolution_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        ((u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) = 0 := by
  have hu :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
      u.property
  have hCanonical :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        f).property
  rw [inner_sub_right, hu, hCanonical, sub_self]

/-- Exact Dirichlet energy-gap identity on the actual beta-zero
Gibbs-vacuum orthogonal sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_quadraticGap
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
    continuousLinearMap_dirichletEnergy_sub_solution_eq_quadraticGap
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
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2,
    continuousLinearMapDirichletEnergy,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply] using
    hGap

/-- The exact energy gap controls squared distance to the canonical centered
solution with coefficient `1 / 648`, equivalently strong-convexity modulus
`1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_648_mul_norm_sq_sub_canonical_le_randomScanPoissonDirichletEnergyL2_sub_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 648) *
        ‖(u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_quadraticGap]
  have hLower :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonOperatorL2_quadraticForm_of_inner_vacuum_eq_zero
      ((u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_sub_randomScanCanonicalPoissonSolution_eq_zero
        f u)
  nlinarith

/-- The Euler--Lagrange condition for the actual centered Dirichlet problem. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystemBetaZeroRandomScanPoissonDirichletEulerLagrangeL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : Prop :=
  ∀ v : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
        (v : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0

/-- On `Ω⊥`, the Euler--Lagrange condition is exactly the centered Poisson
equation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEulerLagrangeL2_iff_poisson_eq_centering
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystemBetaZeroRandomScanPoissonDirichletEulerLagrangeL2
        f u ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
  constructor
  · intro hEuler
    let r : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f
    have hrEq :
        r =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            ((u : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
                f) := by
      simp only [r, map_sub,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2]
    have hrMem :
        r ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 := by
      rw [hrEq]
      exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_mem_vacuumOrthogonalSubmoduleL2
          ((u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f)
    let rv : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
      ⟨r, hrMem⟩
    have hrr : inner ℝ r r = 0 := by
      simpa only [rv, r] using hEuler rv
    rw [real_inner_self_eq_norm_sq] at hrr
    have hrNorm : ‖r‖ = 0 := by
      nlinarith [norm_nonneg r]
    have hrZero : r = 0 := norm_eq_zero.mp hrNorm
    apply sub_eq_zero.mp
    simpa only [r] using hrZero
  · intro hPoisson v
    rw [hPoisson, sub_self]
    simp

/-- The centered Poisson equation has exactly the canonical generalized-inverse
solution on `Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_centering_iff_eq_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f := by
  have hCanonicalPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
    rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_centeringEndL2
        f
  constructor
  · intro hPoisson
    have hADiff :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            ((u : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
                f : Lp ℝ 2
                  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) = 0 := by
      rw [map_sub, hPoisson, hCanonicalPoisson, sub_self]
    have hLower :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonOperatorL2_quadraticForm_of_inner_vacuum_eq_zero
        ((u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_sub_randomScanCanonicalPoissonSolution_eq_zero
          f u)
    rw [hADiff] at hLower
    simp at hLower
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
    exact hCanonicalPoisson

/-- The canonical centered solution is a global minimizer of the actual
Dirichlet energy on `Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_canonical_le
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f) ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
        f u := by
  have hStrong :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_648_mul_norm_sq_sub_canonical_le_randomScanPoissonDirichletEnergyL2_sub_canonical
      f u
  have hNonneg :
      0 ≤ ((1 : ℝ) / 648) *
        ‖(u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 := by
    positivity
  linarith

/-- Equality with the minimum Dirichlet energy occurs exactly at the canonical
centered solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_eq_canonical_iff_eq_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f := by
  constructor
  · intro hEnergy
    have hStrong :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_648_mul_norm_sq_sub_canonical_le_randomScanPoissonDirichletEnergyL2_sub_canonical
        f u
    rw [hEnergy, sub_self] at hStrong
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

/-- Equality with the minimum energy is equivalent to the centered Poisson
equation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_eq_canonical_iff_poisson_eq_centering
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ↔
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_eq_canonical_iff_eq_canonical
      f u).trans
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_centering_iff_eq_canonical
        f u).symm

/-- The Euler--Lagrange condition is equivalent to being the unique canonical
centered minimizer. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEulerLagrangeL2_iff_eq_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystemBetaZeroRandomScanPoissonDirichletEulerLagrangeL2
        f u ↔
      u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEulerLagrangeL2_iff_poisson_eq_centering
      f u).trans
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_centering_iff_eq_canonical
        f u)

/-- Structured receipt for the actual beta-zero Poisson--Dirichlet variational
principle on the Gibbs-vacuum orthogonal sector. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletPrincipleL2Receipt :
    Prop where
  exact_energy_gap :
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
  strong_convexity_gap :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ((1 : ℝ) / 648) *
          ‖(u : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f)
  euler_lagrange_iff_poisson :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystemBetaZeroRandomScanPoissonDirichletEulerLagrangeL2
          f u ↔
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f
  unique_minimizer :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) ↔
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f

/-- The actual finite-volume side-three periodic `SU(2)`, beta-zero random-scan
system satisfies the full Poisson--Dirichlet variational receipt. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletPrincipleL2_receipt :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletPrincipleL2Receipt := by
  exact
    { exact_energy_gap :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_quadraticGap
      strong_convexity_gap :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_648_mul_norm_sq_sub_canonical_le_randomScanPoissonDirichletEnergyL2_sub_canonical
      euler_lagrange_iff_poisson :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEulerLagrangeL2_iff_poisson_eq_centering
      unique_minimizer :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_eq_canonical_iff_eq_canonical }

end

end MathlibAnalytic
end MGAP4D
