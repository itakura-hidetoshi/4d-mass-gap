import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelMaximumRow
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryDobrushinSchurL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridPairOneSidedBCF
import Mathlib.Tactic

/-!
# Bidirectional Schur L2 bound for finite nonnegative influence kernels

The physical high-temperature spine already produces strict source-column
contraction for a concrete nonnegative influence kernel. Turning such
bounded-test information into an L2 profile estimate requires a genuine Schur
step: both row and column control must be visible.

This file isolates that finite-dimensional algebra for the repository generic
FiniteNonnegativeInfluenceKernelData.

For a nonnegative matrix K, row sums bounded by r, and column sums bounded by c,

sum_i (sum_j K(i,j) v(j))^2 <= r*c * sum_j v(j)^2.

Using the exact maximum row and column sums gives a canonical bidirectional
coefficient alpha(K) and therefore an L2 operator estimate with alpha(K)^2.

The final theorem feeds this bound directly into the already integrated
one-sided profile coercivity theorem. No Wilson-specific row estimate is
asserted here: that remains a model-facing obligation for the positive-beta
physical bridge.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteNonnegativeSchur

/-- Finite Schur test for a nonnegative real matrix with separate row and
column bounds. -/
theorem action_sq_sum_le_row_mul_column
    {ι : Type*}
    [Fintype ι]
    (matrix : ι → ι → ℝ)
    (matrix_nonneg : ∀ i j, 0 ≤ matrix i j)
    (rowBound columnBound : ℝ)
    (rowBound_nonneg : 0 ≤ rowBound)
    (rowSum_le : ∀ i, ∑ j, matrix i j ≤ rowBound)
    (columnSum_le : ∀ j, ∑ i, matrix i j ≤ columnBound)
    (vector : ι → ℝ) :
    (∑ i, (∑ j, matrix i j * vector j) ^ 2) ≤
      rowBound * columnBound * ∑ j, vector j ^ 2 := by
  classical
  have hRowWise : ∀ i,
      (∑ j, matrix i j * vector j) ^ 2 ≤
        rowBound * ∑ j, matrix i j * vector j ^ 2 := by
    intro i
    exact row_action_sq_le
      matrix matrix_nonneg rowBound rowSum_le vector i
  have hDouble :
      (∑ i, ∑ j, matrix i j * vector j ^ 2) ≤
        columnBound * ∑ j, vector j ^ 2 := by
    calc
      (∑ i, ∑ j, matrix i j * vector j ^ 2) =
          ∑ j, ∑ i, matrix i j * vector j ^ 2 := by
        rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, matrix i j) * vector j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.sum_mul]
      _ ≤ ∑ j, columnBound * vector j ^ 2 := by
        apply Finset.sum_le_sum
        intro j _hj
        exact mul_le_mul_of_nonneg_right
          (columnSum_le j) (sq_nonneg (vector j))
      _ = columnBound * ∑ j, vector j ^ 2 := by
        rw [Finset.mul_sum]
  calc
    (∑ i, (∑ j, matrix i j * vector j) ^ 2) ≤
        ∑ i, rowBound * ∑ j, matrix i j * vector j ^ 2 :=
      Finset.sum_le_sum fun i _hi => hRowWise i
    _ = rowBound * (∑ i, ∑ j, matrix i j * vector j ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ rowBound * (columnBound * ∑ j, vector j ^ 2) :=
      mul_le_mul_of_nonneg_left hDouble rowBound_nonneg
    _ = rowBound * columnBound * ∑ j, vector j ^ 2 := by
      ring

end FiniteNonnegativeSchur

/-- Canonical two-sided Schur coefficient: the larger of the exact maximum row
and column sums. -/
noncomputable def finiteInfluenceKernelBidirectionalSchurCoefficient
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) : ℝ :=
  max
    (finiteInfluenceKernelMaximumRowSum K)
    (finiteInfluenceKernelMaximumColumnSum K)

/-- The canonical bidirectional Schur coefficient is nonnegative. -/
theorem finiteInfluenceKernelBidirectionalSchurCoefficient_nonneg
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) :
    0 ≤ finiteInfluenceKernelBidirectionalSchurCoefficient K := by
  unfold finiteInfluenceKernelBidirectionalSchurCoefficient
  exact
    (finiteInfluenceKernelMaximumRowSum_nonneg K).trans
      (le_max_left _ _)

/-- Every row sum is bounded by the bidirectional Schur coefficient. -/
theorem finiteInfluenceKernelRowSum_le_bidirectionalSchurCoefficient
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : ι) :
    finiteInfluenceKernelRowSum K target ≤
      finiteInfluenceKernelBidirectionalSchurCoefficient K := by
  exact
    (finiteInfluenceKernelRowSum_le_maximum K target).trans
      (le_max_left _ _)

/-- Every column sum is bounded by the bidirectional Schur coefficient. -/
theorem finiteInfluenceKernelColumnSum_le_bidirectionalSchurCoefficient
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (source : ι) :
    finiteInfluenceKernelColumnSum K source ≤
      finiteInfluenceKernelBidirectionalSchurCoefficient K := by
  exact
    (finiteInfluenceKernelColumnSum_le_maximum K source).trans
      (le_max_right _ _)

/-- The exact maximum row/column data give a canonical L2 Schur estimate for
every finite nonnegative influence kernel. -/
theorem finiteInfluenceKernel_action_sq_sum_le_bidirectionalSchurCoefficient_sq
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (vector : ι → ℝ) :
    (∑ target,
      (∑ source, K.influence target source * vector source) ^ 2) ≤
      (finiteInfluenceKernelBidirectionalSchurCoefficient K) ^ 2 *
        ∑ source, vector source ^ 2 := by
  have h :=
    FiniteNonnegativeSchur.action_sq_sum_le_row_mul_column
      K.influence
      K.influence_nonneg
      (finiteInfluenceKernelBidirectionalSchurCoefficient K)
      (finiteInfluenceKernelBidirectionalSchurCoefficient K)
      (finiteInfluenceKernelBidirectionalSchurCoefficient_nonneg K)
      (finiteInfluenceKernelRowSum_le_bidirectionalSchurCoefficient K)
      (finiteInfluenceKernelColumnSum_le_bidirectionalSchurCoefficient K)
      vector
  simpa [pow_two, mul_assoc] using h

/-- Strictness of the bidirectional Schur coefficient is exactly simultaneous
strictness of the maximum row and column sums. -/
theorem finiteInfluenceKernelBidirectionalSchurCoefficient_lt_one_iff
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) :
    finiteInfluenceKernelBidirectionalSchurCoefficient K < 1 ↔
      finiteInfluenceKernelMaximumRowSum K < 1 ∧
      finiteInfluenceKernelMaximumColumnSum K < 1 := by
  simp [finiteInfluenceKernelBidirectionalSchurCoefficient, max_lt_iff]

/-- A strict bidirectional influence coefficient plus a componentwise one-sided
profile inequality yields the dimension-free squared profile coercivity used by
the existing pair-residual/Poincare bridge. -/
theorem finiteInfluenceKernelBidirectional_oneSided_global_energy_coercive
    {ι : Type*}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCoefficientLtOne :
      finiteInfluenceKernelBidirectionalSchurCoefficient K < 1)
    (profile localProfile : ι → ℝ)
    (hProfileNonneg : ∀ i, 0 ≤ profile i)
    (hLocalNonneg : ∀ i, 0 ≤ localProfile i)
    (hOneSided : ∀ i,
      profile i ≤
        localProfile i + ∑ j, K.influence i j * profile j) :
    (1 - finiteInfluenceKernelBidirectionalSchurCoefficient K) ^ 2 *
        ∑ i, profile i ^ 2 ≤
      ∑ i, localProfile i ^ 2 := by
  exact
    FiniteSchurOneSidedProfile.global_energy_coercive
      K.influence
      (finiteInfluenceKernelBidirectionalSchurCoefficient K)
      (finiteInfluenceKernelBidirectionalSchurCoefficient_nonneg K)
      hCoefficientLtOne
      K.influence_nonneg
      (finiteInfluenceKernel_action_sq_sum_le_bidirectionalSchurCoefficient_sq
        K)
      profile localProfile hProfileNonneg hLocalNonneg hOneSided

end

end MGAP4D.MathlibAnalytic
