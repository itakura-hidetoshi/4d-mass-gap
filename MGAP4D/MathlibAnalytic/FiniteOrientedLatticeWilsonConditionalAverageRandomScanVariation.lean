import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalAverageVariationSum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Linkwise variation obtained by averaging the exact one-target Dobrushin
updates uniformly over all physical target links. -/
noncomputable def finiteOrientedConditionalAverageRandomScanVariation
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (source : L.Edge) : ℝ :=
  (Fintype.card L.Edge : ℝ)⁻¹ *
    ∑ target : L.Edge,
      finiteOrientedConditionalAverageUpdatedVariation
        D variation target source

/-- The random-scan variation remains nonnegative. -/
theorem finiteOrientedConditionalAverageRandomScanVariation_nonneg
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (source : L.Edge) :
    0 ≤ finiteOrientedConditionalAverageRandomScanVariation
      D variation source := by
  unfold finiteOrientedConditionalAverageRandomScanVariation
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun target _htarget =>
      finiteOrientedConditionalAverageUpdatedVariation_nonneg
        D variation hVariation target source)

/-- Summing the random-scan variation commutes the source and target sums. -/
theorem finiteOrientedConditionalAverageRandomScanVariation_sum_eq
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ) :
    (∑ source : L.Edge,
      finiteOrientedConditionalAverageRandomScanVariation
        D variation source) =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ target : L.Edge, ∑ source : L.Edge,
          finiteOrientedConditionalAverageUpdatedVariation
            D variation target source := by
  classical
  unfold finiteOrientedConditionalAverageRandomScanVariation
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

/-- The explicit uniform random-scan contraction factor. -/
def finiteOrientedConditionalAverageRandomScanContractionFactor
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) : ℝ :=
  1 - (1 - D.dobrushinCoefficient) *
    (Fintype.card L.Edge : ℝ)⁻¹

/-- The random-scan factor is strictly below one whenever the finite physical
link carrier is nonempty. -/
theorem finiteOrientedConditionalAverageRandomScanContractionFactor_lt_one
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteOrientedConditionalAverageRandomScanContractionFactor D < 1 := by
  have hCard : 0 < (Fintype.card L.Edge : ℝ) := by
    exact_mod_cast hEdge
  have hGap : 0 < 1 - D.dobrushinCoefficient := by
    linarith [D.dobrushinCoefficient_lt_one]
  have hProduct :
      0 < (1 - D.dobrushinCoefficient) *
        (Fintype.card L.Edge : ℝ)⁻¹ :=
    mul_pos hGap (inv_pos.mpr hCard)
  unfold finiteOrientedConditionalAverageRandomScanContractionFactor
  linarith

/-- Uniform random scan contracts the total link-variation mass by the explicit
factor `1 - (1-c)/N`, where `c` is the Dobrushin coefficient and `N` is the
number of physical links. -/
theorem finiteOrientedConditionalAverageRandomScanVariation_sum_le
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e) :
    (∑ source : L.Edge,
      finiteOrientedConditionalAverageRandomScanVariation
        D variation source) ≤
      finiteOrientedConditionalAverageRandomScanContractionFactor D *
        ∑ source : L.Edge, variation source := by
  classical
  let total : ℝ := ∑ source : L.Edge, variation source
  let gap : ℝ := 1 - D.dobrushinCoefficient
  let card : ℝ := Fintype.card L.Edge
  have hEach : ∀ target : L.Edge,
      (∑ source : L.Edge,
        finiteOrientedConditionalAverageUpdatedVariation
          D variation target source) ≤
        total - gap * variation target := by
    intro target
    simpa [total, gap] using
      finiteOrientedConditionalAverageUpdatedVariation_sum_le
        D variation hVariation target
  have hSummed :
      (∑ target : L.Edge, ∑ source : L.Edge,
        finiteOrientedConditionalAverageUpdatedVariation
          D variation target source) ≤
        ∑ target : L.Edge, (total - gap * variation target) := by
    apply Finset.sum_le_sum
    intro target _htarget
    exact hEach target
  have hRight :
      (∑ target : L.Edge, (total - gap * variation target)) =
        card * total - gap * total := by
    simp [total, gap, card, Finset.sum_sub_distrib,
      Finset.mul_sum]
    ring
  have hInvNonneg : 0 ≤ card⁻¹ := by
    exact inv_nonneg.mpr (by
      dsimp [card]
      positivity)
  calc
    (∑ source : L.Edge,
      finiteOrientedConditionalAverageRandomScanVariation
        D variation source) =
      card⁻¹ *
        ∑ target : L.Edge, ∑ source : L.Edge,
          finiteOrientedConditionalAverageUpdatedVariation
            D variation target source := by
      simpa [card] using
        finiteOrientedConditionalAverageRandomScanVariation_sum_eq
          D variation
    _ ≤ card⁻¹ *
        ∑ target : L.Edge, (total - gap * variation target) :=
      mul_le_mul_of_nonneg_left hSummed hInvNonneg
    _ = card⁻¹ * (card * total - gap * total) := by
      rw [hRight]
    _ = finiteOrientedConditionalAverageRandomScanContractionFactor D *
        ∑ source : L.Edge, variation source := by
      have hCardNe : card ≠ 0 := by
        dsimp [card]
        exact_mod_cast (Nat.ne_of_gt hEdge)
      unfold finiteOrientedConditionalAverageRandomScanContractionFactor
      dsimp [card, gap, total]
      field_simp [hCardNe]
      ring

end

end MathlibAnalytic
end MGAP4D
