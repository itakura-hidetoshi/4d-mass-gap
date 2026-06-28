import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinTotalVariationContraction
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinRandomScanScale

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

noncomputable def finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (source : L.Edge) : ℝ :=
  (Fintype.card L.Edge : ℝ)⁻¹ *
    ∑ target : L.Edge,
      finiteOrientedLatticeWilsonDobrushinUpdatedVariation
        D variation target source

theorem finite_oriented_dobrushinRandomScanUpdatedVariation_nonneg
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (source : L.Edge) :
    0 ≤ finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
      D variation source := by
  unfold finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun target _ =>
      finite_oriented_dobrushinUpdatedVariation_nonneg
        D variation hVariation target source)

theorem finite_oriented_dobrushinRandomScanUpdatedVariation_total_eq
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ) :
    finiteOrientedLatticeWilsonTotalVariation
        (finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
          D variation) =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ target : L.Edge,
          finiteOrientedLatticeWilsonTotalVariation
            (finiteOrientedLatticeWilsonDobrushinUpdatedVariation
              D variation target) := by
  classical
  unfold finiteOrientedLatticeWilsonTotalVariation
    finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

theorem finite_oriented_dobrushinRandomScanUpdatedVariation_total_le_rate_mul
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteOrientedLatticeWilsonTotalVariation
        (finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
          D variation) ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanRate L D *
        finiteOrientedLatticeWilsonTotalVariation variation := by
  let n : ℝ := Fintype.card L.Edge
  let total : ℝ := finiteOrientedLatticeWilsonTotalVariation variation
  let gap : ℝ := finiteOrientedLatticeWilsonDobrushinHeatBathGap D
  have hCardPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hCardNe : n ≠ 0 := ne_of_gt hCardPos
  have hInvNonneg : 0 ≤ n⁻¹ := inv_nonneg.mpr (le_of_lt hCardPos)
  have hTargetSum :
      (∑ target : L.Edge,
          finiteOrientedLatticeWilsonTotalVariation
            (finiteOrientedLatticeWilsonDobrushinUpdatedVariation
              D variation target)) ≤
        ∑ target : L.Edge, (total - gap * variation target) := by
    apply Finset.sum_le_sum
    intro target _htarget
    exact finite_oriented_dobrushinUpdatedVariation_total_le
      D variation hVariation target
  have hConstSum : (∑ _target : L.Edge, total) = n * total := by
    simp [n, nsmul_eq_mul]
  have hDropSum :
      (∑ target : L.Edge, gap * variation target) = gap * total := by
    unfold total finiteOrientedLatticeWilsonTotalVariation
    rw [← Finset.mul_sum]
  rw [finite_oriented_dobrushinRandomScanUpdatedVariation_total_eq]
  change n⁻¹ *
      (∑ target : L.Edge,
        finiteOrientedLatticeWilsonTotalVariation
          (finiteOrientedLatticeWilsonDobrushinUpdatedVariation
            D variation target)) ≤
    finiteOrientedLatticeWilsonDobrushinRandomScanRate L D * total
  calc
    n⁻¹ *
        (∑ target : L.Edge,
          finiteOrientedLatticeWilsonTotalVariation
            (finiteOrientedLatticeWilsonDobrushinUpdatedVariation
              D variation target)) ≤
      n⁻¹ * ∑ target : L.Edge, (total - gap * variation target) :=
      mul_le_mul_of_nonneg_left hTargetSum hInvNonneg
    _ = n⁻¹ * (n * total - gap * total) := by
      rw [Finset.sum_sub_distrib, hConstSum, hDropSum]
    _ = finiteOrientedLatticeWilsonDobrushinRandomScanRate L D * total := by
      dsimp [n, gap]
      unfold finiteOrientedLatticeWilsonDobrushinRandomScanRate
      field_simp [hCardNe]

end
end MathlibAnalytic
end MGAP4D
