import MGAP4D.MathlibAnalytic.FinitePositiveWeightParallelDisagreementProfile
import MGAP4D.MathlibAnalytic.FinitePositiveWeightNonstrictInfluenceMatrix
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Proof-relevant strict Dobrushin data with a common bound on both influence
rows and influence columns.  Row control feeds the existing random-scan
response layer, while column control is the orientation required by the
correct-marginal parallel coupling. -/
structure FinitePositiveWeightBidirectionalDobrushinL1MatrixData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) where
  influence : ι → ι → ℝ
  influence_nonneg :
    ∀ target source : ι, 0 ≤ influence target source
  influence_diagonal_zero :
    ∀ e : ι, influence e e = 0
  conditionalL1_le :
    ∀ (target source : ι) (A B : ι → G),
      FiniteProductAgreeOff A B source →
        finitePositiveWeightSingleSiteConditionalL1 weight A B target ≤
          influence target source
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  rowSum_le_coefficient :
    ∀ target : ι,
      ∑ source : ι, influence target source ≤ coefficient
  columnSum_le_coefficient :
    ∀ source : ι,
      ∑ target : ι, influence target source ≤ coefficient
  coefficient_lt_one : coefficient < 1

namespace FinitePositiveWeightBidirectionalDobrushinL1MatrixData

variable {ι G : Type}
variable [DecidableEq ι] [Fintype ι] [Fintype G]
variable {weight : (ι → G) → ℝ}

/-- Forget column control and recover the row-oriented Dobrushin package used
by the existing random-scan and response theory. -/
noncomputable def toDobrushinL1MatrixData
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight) :
    FinitePositiveWeightDobrushinL1MatrixData weight :=
  { influence := B.influence
    influence_nonneg := B.influence_nonneg
    influence_diagonal_zero := B.influence_diagonal_zero
    conditionalL1_le := B.conditionalL1_le
    coefficient := B.coefficient
    coefficient_nonneg := B.coefficient_nonneg
    rowSum_le_coefficient := B.rowSum_le_coefficient
    coefficient_lt_one := B.coefficient_lt_one }

/-- Forget strict coefficient data while preserving the common influence
matrix. -/
noncomputable def toNonstrictL1MatrixData
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight) :
    FinitePositiveWeightNonstrictL1MatrixData weight :=
  { influence := B.influence
    influence_nonneg := B.influence_nonneg
    influence_diagonal_zero := B.influence_diagonal_zero
    conditionalL1_le := B.conditionalL1_le }

/-- Every influence row is strictly below one. -/
theorem rowSum_lt_one
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (target : ι) :
    (∑ source : ι, B.influence target source) < 1 :=
  lt_of_le_of_lt (B.rowSum_le_coefficient target) B.coefficient_lt_one

/-- Every influence column is strictly below one. -/
theorem columnSum_lt_one
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (source : ι) :
    (∑ target : ι, B.influence target source) < 1 :=
  lt_of_le_of_lt (B.columnSum_le_coefficient source) B.coefficient_lt_one

/-- For a single-source input discrepancy, the canonical parallel coupling has
total coordinate disagreement bounded by the common coefficient. -/
theorem parallelTotalCoordinateDisagreement_le_coefficient
    [DecidableEq G]
    [Nonempty G]
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (source : ι)
    (hAgree : FiniteProductAgreeOff
      leftEnvironment rightEnvironment source) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        weight hweight leftEnvironment rightEnvironment ≤
      B.coefficient := by
  exact le_trans
    (finitePositiveWeightDobrushin_parallelTotalCoordinateDisagreement_le_columnSum
      weight hweight B.toDobrushinL1MatrixData
      leftEnvironment rightEnvironment source hAgree)
    (B.columnSum_le_coefficient source)

/-- The same single-source parallel disagreement is strictly below one. -/
theorem parallelTotalCoordinateDisagreement_lt_one
    [DecidableEq G]
    [Nonempty G]
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (source : ι)
    (hAgree : FiniteProductAgreeOff
      leftEnvironment rightEnvironment source) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        weight hweight leftEnvironment rightEnvironment < 1 :=
  lt_of_le_of_lt
    (B.parallelTotalCoordinateDisagreement_le_coefficient
      hweight leftEnvironment rightEnvironment source hAgree)
    B.coefficient_lt_one

end FinitePositiveWeightBidirectionalDobrushinL1MatrixData

/-- A non-strict influence matrix plus a common strict row/column bound becomes
bidirectional Dobrushin data. -/
noncomputable def
    FinitePositiveWeightNonstrictL1MatrixData.toBidirectionalDobrushinL1MatrixData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (coefficient : ℝ)
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hRowSum :
      ∀ target : ι,
        finitePositiveWeightNonstrictInfluenceRowSum D target ≤ coefficient)
    (hColumnSum :
      ∀ source : ι,
        finitePositiveWeightNonstrictInfluenceColumnSum D source ≤ coefficient)
    (hCoefficientLtOne : coefficient < 1) :
    FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight :=
  { influence := D.influence
    influence_nonneg := D.influence_nonneg
    influence_diagonal_zero := D.influence_diagonal_zero
    conditionalL1_le := D.conditionalL1_le
    coefficient := coefficient
    coefficient_nonneg := hCoefficientNonneg
    rowSum_le_coefficient := hRowSum
    columnSum_le_coefficient := hColumnSum
    coefficient_lt_one := hCoefficientLtOne }

end

end MathlibAnalytic
end MGAP4D
