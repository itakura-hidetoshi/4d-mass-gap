import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalL1Telescoping
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Two finite product configurations share common exterior data outside a
specified finite interior region. -/
def FiniteProductAgreeOutside
    {ι G : Type}
    (A B : ι → G)
    (interior : Finset ι) : Prop :=
  ∀ i : ι, i ∉ interior → A i = B i

/-- Under common exterior data, every disagreement coordinate lies in the
specified interior region. -/
theorem finiteProductDisagreementFinset_subset_of_agreeOutside
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    (A B : ι → G)
    (interior : Finset ι)
    (hOutside : FiniteProductAgreeOutside A B interior) :
    finiteProductDisagreementFinset A B ⊆ interior := by
  intro i hi
  by_contra hNotInterior
  have hEq := hOutside i hNotInterior
  have hNe : A i ≠ B i := by
    simpa [finiteProductDisagreementFinset] using hi
  exact hNe hEq

/-- Common exterior data bounds the real Hamming distance by the cardinality
of the interior region. -/
theorem finiteProductHammingDistanceReal_le_card_of_agreeOutside
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    (A B : ι → G)
    (interior : Finset ι)
    (hOutside : FiniteProductAgreeOutside A B interior) :
    finiteProductHammingDistanceReal A B ≤ (interior.card : ℝ) := by
  unfold finiteProductHammingDistanceReal
  exact_mod_cast Finset.card_le_card
    (finiteProductDisagreementFinset_subset_of_agreeOutside
      A B interior hOutside)

/-- Generic spatial-sandwich stability: if the two input environments share
common exterior data, the canonical correct-marginal parallel coupling has
total coordinate disagreement bounded by the interior volume times one half
of the common bidirectional coefficient. -/
theorem
    FinitePositiveWeightBidirectionalDobrushinL1MatrixData.parallelSpatialSandwichStability
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (interior : Finset ι)
    (hOutside :
      FiniteProductAgreeOutside leftEnvironment rightEnvironment interior) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        weight hweight leftEnvironment rightEnvironment ≤
      ((2 : ℝ)⁻¹ * B.coefficient) * (interior.card : ℝ) := by
  exact le_trans
    (B.parallelTotalCoordinateDisagreement_le_halfCoefficient_mul_hamming
      hweight leftEnvironment rightEnvironment)
    (mul_le_mul_of_nonneg_left
      (finiteProductHammingDistanceReal_le_card_of_agreeOutside
        leftEnvironment rightEnvironment interior hOutside)
      B.halfCoefficient_nonneg)

/-- The spatial-sandwich contraction factor remains strictly below one. -/
theorem
    FinitePositiveWeightBidirectionalDobrushinL1MatrixData.parallelSpatialSandwichFactor_lt_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight) :
    (2 : ℝ)⁻¹ * B.coefficient < 1 :=
  B.halfCoefficient_lt_one

end

end MathlibAnalytic
end MGAP4D
