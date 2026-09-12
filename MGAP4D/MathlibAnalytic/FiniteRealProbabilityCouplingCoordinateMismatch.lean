import MGAP4D.MathlibAnalytic.FiniteProductKernelCouplingVariation
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCouplingCostSplit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A one-coordinate mismatch indicator is bounded by one. -/
theorem finiteProductMismatchIndicator_le_one
    {ι G : Type}
    (A B : ι → G)
    (source : ι) :
    finiteProductMismatchIndicator A B source ≤ 1 := by
  classical
  by_cases hEq : A source = B source
  · simp [finiteProductMismatchIndicator, hEq]
  · simp [finiteProductMismatchIndicator, hEq]

namespace FiniteRealCouplingData

variable {ι G : Type}
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq G]
  [Fintype G]

/-- Expected disagreement at one displayed product coordinate under a finite
coupling.  Unlike total Hamming cost, this quantity is uniformly bounded by
one independently of the number of coordinates. -/
def expectedFiniteProductCoordinateMismatch
    {P Q : FiniteRealProbabilityData (ι → G)}
    (C : FiniteRealCouplingData P Q)
    (source : ι) : ℝ :=
  C.expectedCost fun A B => finiteProductMismatchIndicator A B source

/-- Expected one-coordinate mismatch is nonnegative. -/
theorem expectedFiniteProductCoordinateMismatch_nonneg
    {P Q : FiniteRealProbabilityData (ι → G)}
    (C : FiniteRealCouplingData P Q)
    (source : ι) :
    0 ≤ C.expectedFiniteProductCoordinateMismatch source := by
  unfold expectedFiniteProductCoordinateMismatch expectedCost
  exact Finset.sum_nonneg fun A _hA =>
    Finset.sum_nonneg fun B _hB =>
      mul_nonneg (C.joint_nonneg A B)
        (finiteProductMismatchIndicator_nonneg A B source)

/-- Every finite coupling has expected mismatch at one coordinate at most one.
This is the dimension-free replacement for the cardinality bound on total
Hamming cost. -/
theorem expectedFiniteProductCoordinateMismatch_le_one
    {P Q : FiniteRealProbabilityData (ι → G)}
    (C : FiniteRealCouplingData P Q)
    (source : ι) :
    C.expectedFiniteProductCoordinateMismatch source ≤ 1 := by
  unfold expectedFiniteProductCoordinateMismatch expectedCost
  calc
    (∑ A : ι → G, ∑ B : ι → G,
      C.joint A B * finiteProductMismatchIndicator A B source) ≤
        ∑ A : ι → G, ∑ B : ι → G, C.joint A B * 1 := by
      apply Finset.sum_le_sum
      intro A _hA
      apply Finset.sum_le_sum
      intro B _hB
      exact mul_le_mul_of_nonneg_left
        (finiteProductMismatchIndicator_le_one A B source)
        (C.joint_nonneg A B)
    _ = ∑ A : ι → G, ∑ B : ι → G, C.joint A B := by
      simp
    _ = 1 := C.totalMass_eq_one

/-- The exact dimension-free interval for one-coordinate mismatch expectation. -/
theorem expectedFiniteProductCoordinateMismatch_mem_Icc
    {P Q : FiniteRealProbabilityData (ι → G)}
    (C : FiniteRealCouplingData P Q)
    (source : ι) :
    C.expectedFiniteProductCoordinateMismatch source ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨C.expectedFiniteProductCoordinateMismatch_nonneg source,
    C.expectedFiniteProductCoordinateMismatch_le_one source⟩

end FiniteRealCouplingData

end

end MathlibAnalytic
end MGAP4D
