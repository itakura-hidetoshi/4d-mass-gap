import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanSpatialSupport
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The length-`m` oriented Dobrushin influence kernel.  The first index is the
initial target link and the second index is the final source link. -/
noncomputable def
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influencePathKernel
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) :
    ℕ → L.Edge → L.Edge → ℝ
  | 0, target, source => if target = source then 1 else 0
  | m + 1, target, source =>
      ∑ middle : L.Edge,
        D.influencePathKernel m target middle *
          D.influence middle source

@[simp] theorem finite_oriented_influencePathKernel_zero
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (target source : L.Edge) :
    D.influencePathKernel 0 target source =
      if target = source then 1 else 0 := rfl

@[simp] theorem finite_oriented_influencePathKernel_succ
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (m : ℕ)
    (target source : L.Edge) :
    D.influencePathKernel (m + 1) target source =
      ∑ middle : L.Edge,
        D.influencePathKernel m target middle *
          D.influence middle source := rfl

/-- Every finite influence-path weight is nonnegative. -/
theorem finite_oriented_influencePathKernel_nonneg
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (m : ℕ)
    (target source : L.Edge) :
    0 ≤ D.influencePathKernel m target source := by
  induction m generalizing target source with
  | zero =>
      simp only [finite_oriented_influencePathKernel_zero]
      split_ifs <;> norm_num
  | succ m ih =>
      rw [finite_oriented_influencePathKernel_succ]
      exact Finset.sum_nonneg fun middle _hMiddle =>
        mul_nonneg (ih target middle)
          (D.influence_nonneg middle source)

/-- Total length-`m` influence mass emitted from one initial physical link. -/
noncomputable def
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influencePathRowMass
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (m : ℕ)
    (target : L.Edge) : ℝ :=
  ∑ source : L.Edge, D.influencePathKernel m target source

/-- The length-zero influence row is the point mass at its initial link. -/
@[simp] theorem finite_oriented_influencePathRowMass_zero
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (target : L.Edge) :
    D.influencePathRowMass 0 target = 1 := by
  classical
  simp [FiniteOrientedLatticeWilsonDobrushinMatrixData.influencePathRowMass]

/-- Influence-path row mass is nonnegative. -/
theorem finite_oriented_influencePathRowMass_nonneg
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (m : ℕ)
    (target : L.Edge) :
    0 ≤ D.influencePathRowMass m target := by
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influencePathRowMass
  exact Finset.sum_nonneg fun source _hSource =>
    finite_oriented_influencePathKernel_nonneg D m target source

/-- One additional path step multiplies the previous row weights by the exact
Dobrushin row sums of their intermediate links. -/
theorem finite_oriented_influencePathRowMass_succ_eq
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (m : ℕ)
    (target : L.Edge) :
    D.influencePathRowMass (m + 1) target =
      ∑ middle : L.Edge,
        D.influencePathKernel m target middle *
          (∑ source : L.Edge, D.influence middle source) := by
  classical
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influencePathRowMass
  rw [finite_oriented_influencePathKernel_succ]
  calc
    (∑ source : L.Edge,
      ∑ middle : L.Edge,
        D.influencePathKernel m target middle *
          D.influence middle source) =
      ∑ middle : L.Edge,
        ∑ source : L.Edge,
          D.influencePathKernel m target middle *
            D.influence middle source := by
      rw [Finset.sum_comm]
    _ = ∑ middle : L.Edge,
        D.influencePathKernel m target middle *
          (∑ source : L.Edge, D.influence middle source) := by
      apply Finset.sum_congr rfl
      intro middle _hMiddle
      rw [Finset.mul_sum]

/-- The row mass of length-`m` influence paths is bounded by the `m`th power of
the strict Dobrushin coefficient. -/
theorem finite_oriented_influencePathRowMass_le_pow
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (m : ℕ)
    (target : L.Edge) :
    D.influencePathRowMass m target ≤
      D.dobrushinCoefficient ^ m := by
  induction m generalizing target with
  | zero => simp
  | succ m ih =>
      rw [finite_oriented_influencePathRowMass_succ_eq]
      calc
        (∑ middle : L.Edge,
          D.influencePathKernel m target middle *
            (∑ source : L.Edge, D.influence middle source)) ≤
          ∑ middle : L.Edge,
            D.influencePathKernel m target middle *
              D.dobrushinCoefficient := by
          apply Finset.sum_le_sum
          intro middle _hMiddle
          exact mul_le_mul_of_nonneg_left
            (D.rowSum_le_coefficient middle)
            (finite_oriented_influencePathKernel_nonneg
              D m target middle)
        _ = D.dobrushinCoefficient *
            D.influencePathRowMass m target := by
          unfold
            FiniteOrientedLatticeWilsonDobrushinMatrixData.influencePathRowMass
          rw [← Finset.sum_mul]
          ring
        _ ≤ D.dobrushinCoefficient *
            D.dobrushinCoefficient ^ m :=
          mul_le_mul_of_nonneg_left
            (ih target) D.dobrushinCoefficient_nonneg
        _ = D.dobrushinCoefficient ^ (m + 1) := by
          rw [pow_succ]
          ring

/-- Every pointwise path weight is bounded by its emitted row mass. -/
theorem finite_oriented_influencePathKernel_le_rowMass
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (m : ℕ)
    (target source : L.Edge) :
    D.influencePathKernel m target source ≤
      D.influencePathRowMass m target := by
  classical
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influencePathRowMass
  exact Finset.single_le_sum
    (fun e _he =>
      finite_oriented_influencePathKernel_nonneg D m target e)
    (Finset.mem_univ source)

/-- Consequently, each length-`m` pointwise influence is at most `c^m`. -/
theorem finite_oriented_influencePathKernel_le_pow
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (m : ℕ)
    (target source : L.Edge) :
    D.influencePathKernel m target source ≤
      D.dobrushinCoefficient ^ m :=
  le_trans
    (finite_oriented_influencePathKernel_le_rowMass
      D m target source)
    (finite_oriented_influencePathRowMass_le_pow D m target)

/-- A length-`m` influence path cannot reach outside the `m`-step active
plaquette-neighbor ball of its initial link. -/
theorem finite_oriented_influencePathKernel_eq_zero_of_not_mem_activeBall
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    (m : ℕ)
    (target source : L.Edge)
    (hSource :
      source ∉ L.activePlaquetteNeighborBall {target} m) :
    D.influencePathKernel m target source = 0 := by
  classical
  induction m generalizing target source with
  | zero =>
      have hNe : target ≠ source := by
        simpa using hSource
      simp [hNe]
  | succ m ih =>
      rw [finite_oriented_influencePathKernel_succ]
      apply Finset.sum_eq_zero
      intro middle _hMiddle
      by_cases hMiddle :
          middle ∈ L.activePlaquetteNeighborBall {target} m
      · have hOutsideExpansion :
            source ∉ L.activePlaquetteNeighborExpansion
              (L.activePlaquetteNeighborBall {target} m) := by
          simpa using hSource
        have hNotActive :
            source ∉ L.activePlaquetteNeighbors middle := by
          intro hActive
          apply hOutsideExpansion
          exact
            (finite_oriented_mem_activePlaquetteNeighborExpansion_iff
              L (L.activePlaquetteNeighborBall {target} m) source).2
              (Or.inr ⟨middle, hMiddle, hActive⟩)
        have hInfluence : D.influence middle source = 0 :=
          S.influence_eq_zero_of_not_mem_active
            middle source hNotActive
        rw [hInfluence, mul_zero]
      · have hKernel :
            D.influencePathKernel m target middle = 0 :=
          ih target middle hMiddle
        rw [hKernel, zero_mul]

/-- The pointwise tail of influence paths of lengths `d, d+1, ...`. -/
noncomputable def
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influenceGreenTail
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (d : ℕ)
    (target source : L.Edge) : ℝ :=
  ∑' r : ℕ, D.influencePathKernel (d + r) target source

/-- The emitted row-mass tail of influence paths of lengths `d, d+1, ...`. -/
noncomputable def
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influenceGreenRowTail
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (d : ℕ)
    (target : L.Edge) : ℝ :=
  ∑' r : ℕ, D.influencePathRowMass (d + r) target

/-- The shifted geometric majorant has the explicit sum `c^d / (1-c)`. -/
theorem finite_oriented_dobrushin_geometric_tail_hasSum
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (d : ℕ) :
    HasSum
      (fun r : ℕ => D.dobrushinCoefficient ^ (d + r))
      (D.dobrushinCoefficient ^ d /
        (1 - D.dobrushinCoefficient)) := by
  have hNorm : ‖D.dobrushinCoefficient‖ < 1 := by
    simpa [Real.norm_eq_abs,
      abs_of_nonneg D.dobrushinCoefficient_nonneg] using
      D.dobrushinCoefficient_lt_one
  have hGeom :=
    (hasSum_geometric_of_norm_lt_one hNorm).mul_left
      (D.dobrushinCoefficient ^ d)
  simpa [pow_add, div_eq_mul_inv] using hGeom

/-- The row-mass Green tail is summable. -/
theorem finite_oriented_influenceGreenRowTail_summable
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (d : ℕ)
    (target : L.Edge) :
    Summable fun r : ℕ =>
      D.influencePathRowMass (d + r) target := by
  refine Summable.of_nonneg_of_le
    (fun r =>
      finite_oriented_influencePathRowMass_nonneg
        D (d + r) target)
    (fun r =>
      finite_oriented_influencePathRowMass_le_pow
        D (d + r) target)
    (finite_oriented_dobrushin_geometric_tail_hasSum D d).summable

/-- The pointwise Green tail is summable. -/
theorem finite_oriented_influenceGreenTail_summable
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (d : ℕ)
    (target source : L.Edge) :
    Summable fun r : ℕ =>
      D.influencePathKernel (d + r) target source := by
  refine Summable.of_nonneg_of_le
    (fun r =>
      finite_oriented_influencePathKernel_nonneg
        D (d + r) target source)
    (fun r =>
      finite_oriented_influencePathKernel_le_rowMass
        D (d + r) target source)
    (finite_oriented_influenceGreenRowTail_summable D d target)

/-- The complete row-mass contribution from all path lengths at least `d` is
bounded by the explicit geometric tail `c^d / (1-c)`. -/
theorem finite_oriented_influenceGreenRowTail_le
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (d : ℕ)
    (target : L.Edge) :
    D.influenceGreenRowTail d target ≤
      D.dobrushinCoefficient ^ d /
        (1 - D.dobrushinCoefficient) := by
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influenceGreenRowTail
  calc
    (∑' r : ℕ, D.influencePathRowMass (d + r) target) ≤
        ∑' r : ℕ, D.dobrushinCoefficient ^ (d + r) :=
      Summable.tsum_le_tsum
        (fun r =>
          finite_oriented_influencePathRowMass_le_pow
            D (d + r) target)
        (finite_oriented_influenceGreenRowTail_summable D d target)
        (finite_oriented_dobrushin_geometric_tail_hasSum D d).summable
    _ = D.dobrushinCoefficient ^ d /
        (1 - D.dobrushinCoefficient) :=
      (finite_oriented_dobrushin_geometric_tail_hasSum D d).tsum_eq

/-- Every pointwise Green tail is bounded by the corresponding row tail. -/
theorem finite_oriented_influenceGreenTail_le_rowTail
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (d : ℕ)
    (target source : L.Edge) :
    D.influenceGreenTail d target source ≤
      D.influenceGreenRowTail d target := by
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influenceGreenTail
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influenceGreenRowTail
  exact Summable.tsum_le_tsum
    (fun r =>
      finite_oriented_influencePathKernel_le_rowMass
        D (d + r) target source)
    (finite_oriented_influenceGreenTail_summable D d target source)
    (finite_oriented_influenceGreenRowTail_summable D d target)

/-- Every pointwise Green tail therefore obeys the same explicit geometric
majorant. -/
theorem finite_oriented_influenceGreenTail_le
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (d : ℕ)
    (target source : L.Edge) :
    D.influenceGreenTail d target source ≤
      D.dobrushinCoefficient ^ d /
        (1 - D.dobrushinCoefficient) :=
  le_trans
    (finite_oriented_influenceGreenTail_le_rowTail
      D d target source)
    (finite_oriented_influenceGreenRowTail_le D d target)

end

end MathlibAnalytic
end MGAP4D
