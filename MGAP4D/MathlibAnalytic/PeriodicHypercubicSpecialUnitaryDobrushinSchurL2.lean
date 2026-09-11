import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitarySymmetricDobrushin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteNonnegativeSchur

/-- Weighted Cauchy--Schwarz for one row of a nonnegative finite matrix. -/
theorem row_action_sq_le
    {ι : Type*}
    [Fintype ι]
    (matrix : ι → ι → ℝ)
    (matrix_nonneg : ∀ i j, 0 ≤ matrix i j)
    (rowBound : ℝ)
    (rowSum_le : ∀ i, ∑ j, matrix i j ≤ rowBound)
    (vector : ι → ℝ)
    (i : ι) :
    (∑ j, matrix i j * vector j) ^ 2 ≤
      rowBound * ∑ j, matrix i j * vector j ^ 2 := by
  classical
  have hCauchy :
      (∑ j, matrix i j * vector j) ^ 2 ≤
        (∑ j, matrix i j) *
          ∑ j, matrix i j * vector j ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro j _hj
      exact matrix_nonneg i j
    · intro j _hj
      exact mul_nonneg (matrix_nonneg i j) (sq_nonneg (vector j))
    · intro j _hj
      ring
  calc
    (∑ j, matrix i j * vector j) ^ 2 ≤
        (∑ j, matrix i j) *
          ∑ j, matrix i j * vector j ^ 2 := hCauchy
    _ ≤ rowBound * ∑ j, matrix i j * vector j ^ 2 :=
      mul_le_mul_of_nonneg_right (rowSum_le i)
        (Finset.sum_nonneg fun j _hj =>
          mul_nonneg (matrix_nonneg i j) (sq_nonneg (vector j)))

end FiniteNonnegativeSchur

/-- The explicit periodic compact-Haar `SU(N)` influence matrix, exposed as a
finite real matrix for downstream Schur estimates. -/
noncomputable def periodicHypercubicSpecialUnitaryDobrushinInfluence
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    PeriodicHypercubicEdge n → PeriodicHypercubicEdge n → ℝ :=
  specialUnitaryCompactOrientedSharedPlaquetteInfluence
    (periodicHypercubicFiniteOrientedGeometry n)
    N hN beta beta_nonneg

/-- The volume-independent periodic `SU(N)` Dobrushin coefficient. -/
def periodicHypercubicSpecialUnitaryDobrushinCoefficient
    (beta : ℝ) : ℝ :=
  18 * periodicHypercubicSpecialUnitaryDobrushinEta beta

/-- The explicit periodic `SU(N)` influence matrix is pointwise nonnegative. -/
theorem periodicHypercubicSpecialUnitaryDobrushinInfluence_nonneg
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n) :
    0 ≤ periodicHypercubicSpecialUnitaryDobrushinInfluence
      n N hN beta beta_nonneg target source :=
  specialUnitaryCompactOrientedSharedPlaquetteInfluence_nonneg
    (periodicHypercubicFiniteOrientedGeometry n)
    N hN beta beta_nonneg target source

/-- Every row of the explicit periodic `SU(N)` influence matrix is bounded by
its volume-independent Dobrushin coefficient. -/
theorem periodicHypercubicSpecialUnitaryDobrushinInfluence_rowSum_le
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    (∑ source, periodicHypercubicSpecialUnitaryDobrushinInfluence
      n N hN beta beta_nonneg target source) ≤
      periodicHypercubicSpecialUnitaryDobrushinCoefficient beta := by
  exact periodicHypercubicSpecialUnitary_influence_rowSum_le
    n N hn hN beta beta_nonneg target

/-- Finite Schur estimate for the actual periodic compact-Haar `SU(N)`
Dobrushin matrix. Its `ℓ²` operator norm is at most the same volume-independent
coefficient controlling the row and column sums. -/
theorem periodicHypercubicSpecialUnitaryDobrushinInfluence_l2_sq_le
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (vector : PeriodicHypercubicEdge n → ℝ) :
    (∑ target,
      (∑ source,
        periodicHypercubicSpecialUnitaryDobrushinInfluence
          n N hN beta beta_nonneg target source * vector source) ^ 2) ≤
      periodicHypercubicSpecialUnitaryDobrushinCoefficient beta ^ 2 *
        ∑ source, vector source ^ 2 := by
  classical
  let matrix := periodicHypercubicSpecialUnitaryDobrushinInfluence
    n N hN beta beta_nonneg
  let coefficient := periodicHypercubicSpecialUnitaryDobrushinCoefficient beta
  have hCoefficient : 0 ≤ coefficient := by
    dsimp [coefficient, periodicHypercubicSpecialUnitaryDobrushinCoefficient]
    exact mul_nonneg (by norm_num)
      (compactHaarOscillationInfluence_nonneg (by positivity))
  have hRows : ∀ target,
      (∑ source, matrix target source) ≤ coefficient := by
    intro target
    exact periodicHypercubicSpecialUnitaryDobrushinInfluence_rowSum_le
      n N hn hN beta beta_nonneg target
  have hMatrix : ∀ target source, 0 ≤ matrix target source := by
    intro target source
    exact periodicHypercubicSpecialUnitaryDobrushinInfluence_nonneg
      n N hN beta beta_nonneg target source
  have hRowWise : ∀ target,
      (∑ source, matrix target source * vector source) ^ 2 ≤
        coefficient * ∑ source,
          matrix target source * vector source ^ 2 := by
    intro target
    exact FiniteNonnegativeSchur.row_action_sq_le
      matrix hMatrix coefficient hRows vector target
  have hProfile :=
    periodicHypercubicSpecialUnitary_influence_l1_le
      n N hn hN beta beta_nonneg
      (fun source => vector source ^ 2)
      (fun source => sq_nonneg (vector source))
  change
    (∑ target, (∑ source, matrix target source * vector source) ^ 2) ≤
      coefficient ^ 2 * ∑ source, vector source ^ 2
  calc
    (∑ target, (∑ source, matrix target source * vector source) ^ 2) ≤
        ∑ target, coefficient *
          ∑ source, matrix target source * vector source ^ 2 := by
      exact Finset.sum_le_sum fun target _hTarget => hRowWise target
    _ = coefficient *
        (∑ target, ∑ source,
          matrix target source * vector source ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ coefficient *
        (coefficient * ∑ source, vector source ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [matrix, coefficient,
          periodicHypercubicSpecialUnitaryDobrushinInfluence,
          periodicHypercubicSpecialUnitaryDobrushinCoefficient] using hProfile
      · exact hCoefficient
    _ = coefficient ^ 2 * ∑ source, vector source ^ 2 := by
      ring

end

end MathlibAnalytic
end MGAP4D
