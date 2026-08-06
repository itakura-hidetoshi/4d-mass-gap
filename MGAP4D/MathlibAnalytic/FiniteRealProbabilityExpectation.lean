import MGAP4D.MathlibAnalytic.FiniteKernelGroundStateDoobPosteriorProbability
import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryRandomScanComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteRealProbabilityData

variable {α : Type} [Fintype α]

/-- Expected value of a real observable under a finite real probability law. -/
def expectation
    (P : FiniteRealProbabilityData α)
    (f : α → ℝ) : ℝ :=
  ∑ x : α, P.probability x * f x

/-- Expectation is determined pointwise by the probability function. -/
theorem expectation_eq_of_probability_eq
    (P Q : FiniteRealProbabilityData α)
    (hProbability : ∀ x : α, P.probability x = Q.probability x)
    (f : α → ℝ) :
    P.expectation f = Q.expectation f := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _hx
  rw [hProbability x]

/-- The expectation of the constant-one observable is one. -/
theorem expectation_one
    (P : FiniteRealProbabilityData α) :
    P.expectation (fun _ : α => (1 : ℝ)) = 1 := by
  simpa [expectation] using P.probability_sum_eq_one

end FiniteRealProbabilityData

/-- Packaging a positive finite-product weight as a probability law does not
change its normalized global expectation. -/
theorem finiteRealWeightProbabilityData_expectation_eq_globalExpectation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ) :
    (finiteRealWeightProbabilityData
      weight
      (fun A => le_of_lt (hweight A))
      (by
        simpa [finiteRealWeightPartition, finitePositiveWeightTotalMass] using
          finitePositiveWeightTotalMass_pos weight hweight)).expectation f =
      finitePositiveWeightGlobalExpectation weight f := by
  classical
  unfold FiniteRealProbabilityData.expectation
    finiteRealWeightProbabilityData
    finiteRealWeightProbability
    finitePositiveWeightGlobalExpectation
    finitePositiveWeightGlobalProbability
    finitePositiveWeightTotalMass
    finiteRealWeightPartition
  rfl

/-- The preceding expectation identification is independent of the chosen
proofs of nonnegativity and positive partition. -/
theorem finiteRealWeightProbabilityData_expectation_eq_globalExpectation_of_proofs
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 ≤ weight A)
    (hPartition : 0 < finiteRealWeightPartition weight)
    (f : (ι → G) → ℝ) :
    (finiteRealWeightProbabilityData weight hweight hPartition).expectation f =
      finitePositiveWeightGlobalExpectation weight f := by
  classical
  unfold FiniteRealProbabilityData.expectation
    finiteRealWeightProbabilityData
    finiteRealWeightProbability
    finitePositiveWeightGlobalExpectation
    finitePositiveWeightGlobalProbability
    finitePositiveWeightTotalMass
    finiteRealWeightPartition
  rfl

end

end MathlibAnalytic
end MGAP4D
