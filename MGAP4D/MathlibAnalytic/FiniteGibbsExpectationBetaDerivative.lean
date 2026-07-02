import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteGibbsExpectationBetaDerivative

variable {Omega : Type*} [Fintype Omega] [Nonempty Omega]

/-- Unnormalized finite Gibbs weight with convention `exp (-(beta * S))`. -/
def boltzmannWeight (S : Omega -> Real) (beta : Real) (omega : Omega) : Real :=
  Real.exp (-(beta * S omega))

/-- Finite weighted sum against the unnormalized Gibbs weight. -/
def weightedSum (F S : Omega -> Real) (beta : Real) : Real :=
  Finset.univ.sum (fun omega => F omega * boltzmannWeight S beta omega)

/-- Finite partition function. -/
def partitionFunction (S : Omega -> Real) (beta : Real) : Real :=
  weightedSum (fun _ => 1) S beta

/-- Normalized finite Gibbs expectation. -/
def expectation (F S : Omega -> Real) (beta : Real) : Real :=
  weightedSum F S beta / partitionFunction S beta

/-- Gibbs covariance between `F` and the action `S`. -/
def covariance (F S : Omega -> Real) (beta : Real) : Real :=
  expectation (fun omega => F omega * S omega) S beta -
    expectation F S beta * expectation S S beta

/-- Every finite Gibbs weight is strictly positive. -/
theorem boltzmannWeight_pos
    (S : Omega -> Real) (beta : Real) (omega : Omega) :
    0 < boltzmannWeight S beta omega := by
  exact Real.exp_pos _

/-- The finite partition function is strictly positive. -/
theorem partitionFunction_pos
    (S : Omega -> Real) (beta : Real) :
    0 < partitionFunction S beta := by
  classical
  unfold partitionFunction weightedSum boltzmannWeight
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Omega))
      (f := fun omega : Omega => Real.exp (-(beta * S omega)))
      (fun omega _ => Real.exp_pos (-(beta * S omega)))
      Finset.univ_nonempty)

/-- The finite partition function is nonzero. -/
theorem partitionFunction_ne_zero
    (S : Omega -> Real) (beta : Real) :
    Ne (partitionFunction S beta) 0 :=
  ne_of_gt (partitionFunction_pos S beta)

/-- Pointwise derivative of a Gibbs weight. -/
theorem hasDerivAt_boltzmannWeight
    (S : Omega -> Real) (beta : Real) (omega : Omega) :
    HasDerivAt
      (fun t : Real => boltzmannWeight S t omega)
      (boltzmannWeight S beta omega * (-S omega)) beta := by
  have hLinear :
      HasDerivAt (fun t : Real => -(t * S omega)) (-(S omega)) beta :=
    (hasDerivAt_mul_const (x := beta) (S omega)).neg
  simpa [boltzmannWeight] using hLinear.exp

/-- Raw derivative of a finite weighted sum. -/
theorem hasDerivAt_weightedSum_raw
    (F S : Omega -> Real) (beta : Real) :
    HasDerivAt
      (weightedSum F S)
      (Finset.univ.sum fun omega =>
        F omega * (boltzmannWeight S beta omega * (-S omega))) beta := by
  classical
  unfold weightedSum
  apply HasDerivAt.fun_sum
  intro omega _homega
  simpa using
    (hasDerivAt_const beta (F omega)).mul
      (hasDerivAt_boltzmannWeight S beta omega)

/-- Differentiating a finite weighted sum inserts the action with a minus sign. -/
theorem hasDerivAt_weightedSum
    (F S : Omega -> Real) (beta : Real) :
    HasDerivAt
      (weightedSum F S)
      (-weightedSum (fun omega => F omega * S omega) S beta) beta := by
  classical
  have h := hasDerivAt_weightedSum_raw F S beta
  have hDerivative :
      (Finset.univ.sum fun omega : Omega =>
        F omega * (boltzmannWeight S beta omega * (-S omega))) =
        -weightedSum (fun omega => F omega * S omega) S beta := by
    rw [weightedSum, Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro omega _homega
    ring
  rw [hDerivative] at h
  exact h

/-- The partition-function derivative is the negative action-weighted sum. -/
theorem hasDerivAt_partitionFunction
    (S : Omega -> Real) (beta : Real) :
    HasDerivAt
      (partitionFunction S)
      (-weightedSum S S beta) beta := by
  simpa [partitionFunction] using
    (hasDerivAt_weightedSum (fun _ : Omega => 1) S beta)

/-- Finite Gibbs differentiation formula for the convention `exp (-beta S)`. -/
theorem hasDerivAt_expectation_eq_neg_covariance
    (F S : Omega -> Real) (beta : Real) :
    HasDerivAt
      (expectation F S)
      (-covariance F S beta) beta := by
  have hNumerator := hasDerivAt_weightedSum F S beta
  have hDenominator := hasDerivAt_partitionFunction S beta
  have hPartition : Ne (partitionFunction S beta) 0 :=
    partitionFunction_ne_zero S beta
  have hQuotient := hNumerator.div hDenominator hPartition
  unfold expectation covariance
  convert hQuotient using 1
  field_simp [hPartition]
  ring

/-- Derivative form of the finite Gibbs covariance identity. -/
theorem deriv_expectation_eq_neg_covariance
    (F S : Omega -> Real) (beta : Real) :
    deriv (expectation F S) beta = -covariance F S beta :=
  (hasDerivAt_expectation_eq_neg_covariance F S beta).deriv

end FiniteGibbsExpectationBetaDerivative

end

end MathlibAnalytic
end MGAP4D
