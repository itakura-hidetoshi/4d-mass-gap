import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
import Mathlib.Tactic

/-!
# Uniform total mass of the finite random-scan resolvent profile

The finite random-scan profile from the preceding file already satisfies the
transpose-subinvariance inequality

`w_M(source) ≤ v(source) + ∑ target, D(target, source) * w_M(target)`.

Summing this inequality over the physical source links, swapping the two finite
sums, and using the Dobrushin row-sum bound gives directly

`(1 - c) * ∑ source, w_M(source) ≤ ∑ source, v(source)`.

Thus, whenever `c < 1`,

`∑ source, w_M(source) ≤ (1-c)⁻¹ * ∑ source, v(source)`.

No geometric series, infinite Poisson solution, or limiting argument is needed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- For a nonnegative profile, the transpose Dobrushin interaction is bounded
by the row-sum coefficient times its total mass. -/
theorem continuous_compact_oriented_dobrushin_transposeInteraction_le_coefficient_mul_total
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (w : C.base.geometry.Edge → ℝ)
    (hw : ∀ source : C.base.geometry.Edge, 0 ≤ w source) :
    (∑ source : C.base.geometry.Edge,
      ∑ target : C.base.geometry.Edge,
        D.influence target source * w target) ≤
      D.coefficient * continuousCompactOrientedGaugeWilsonTotalVariation w := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ target : C.base.geometry.Edge,
      ∑ source : C.base.geometry.Edge,
        D.influence target source * w target) ≤
      ∑ target : C.base.geometry.Edge, D.coefficient * w target := by
        apply Finset.sum_le_sum
        intro target _
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (D.rowSum_le_coefficient target) (hw target)
    _ = D.coefficient * continuousCompactOrientedGaugeWilsonTotalVariation w := by
      unfold continuousCompactOrientedGaugeWilsonTotalVariation
      rw [← Finset.mul_sum]

/-- The finite normalized random-scan resolvent profile has total mass controlled
by the unnormalized Dobrushin gap, uniformly in the truncation length `M`. -/
theorem continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_gap_mul_total_le
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (M : ℕ) :
    (1 - D.coefficient) *
        continuousCompactOrientedGaugeWilsonTotalVariation
          (continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
            D variation M) ≤
      continuousCompactOrientedGaugeWilsonTotalVariation variation := by
  let w :=
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
      D variation M
  have hw : ∀ source : C.base.geometry.Edge, 0 ≤ w source := by
    intro source
    exact
      continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_nonneg
        D variation hVariation M source
  have hSub : ∀ source : C.base.geometry.Edge,
      w source ≤ variation source +
        ∑ target : C.base.geometry.Edge,
          D.influence target source * w target := by
    intro source
    exact
      continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_subinvariant
        D variation hVariation hEdge M source
  have hSummed :
      continuousCompactOrientedGaugeWilsonTotalVariation w ≤
        continuousCompactOrientedGaugeWilsonTotalVariation variation +
          (∑ source : C.base.geometry.Edge,
            ∑ target : C.base.geometry.Edge,
              D.influence target source * w target) := by
    unfold continuousCompactOrientedGaugeWilsonTotalVariation
    calc
      (∑ source : C.base.geometry.Edge, w source) ≤
          ∑ source : C.base.geometry.Edge,
            (variation source +
              ∑ target : C.base.geometry.Edge,
                D.influence target source * w target) := by
            apply Finset.sum_le_sum
            intro source _
            exact hSub source
      _ = (∑ source : C.base.geometry.Edge, variation source) +
          ∑ source : C.base.geometry.Edge,
            ∑ target : C.base.geometry.Edge,
              D.influence target source * w target := by
            rw [Finset.sum_add_distrib]
  have hInteraction :=
    continuous_compact_oriented_dobrushin_transposeInteraction_le_coefficient_mul_total
      D w hw
  have hTotal :
      continuousCompactOrientedGaugeWilsonTotalVariation w ≤
        continuousCompactOrientedGaugeWilsonTotalVariation variation +
          D.coefficient * continuousCompactOrientedGaugeWilsonTotalVariation w :=
    hSummed.trans (add_le_add_right hInteraction _)
  change
    (1 - D.coefficient) *
        continuousCompactOrientedGaugeWilsonTotalVariation w ≤
      continuousCompactOrientedGaugeWilsonTotalVariation variation
  calc
    (1 - D.coefficient) *
        continuousCompactOrientedGaugeWilsonTotalVariation w =
      continuousCompactOrientedGaugeWilsonTotalVariation w -
        D.coefficient * continuousCompactOrientedGaugeWilsonTotalVariation w := by
          ring
    _ ≤ continuousCompactOrientedGaugeWilsonTotalVariation variation := by
      exact sub_le_iff_le_add.mpr hTotal

/-- Under the strict Dobrushin threshold, the finite random-scan resolvent total
mass is bounded uniformly in `M` by the reciprocal heat-bath gap. -/
theorem continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_total_le_inv_gap_mul
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (hCoefficient : D.coefficient < 1)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (M : ℕ) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
          D variation M) ≤
      (1 - D.coefficient)⁻¹ *
        continuousCompactOrientedGaugeWilsonTotalVariation variation := by
  let w :=
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
      D variation M
  have hGapPos : 0 < 1 - D.coefficient := sub_pos.mpr hCoefficient
  have hGapNe : 1 - D.coefficient ≠ 0 := ne_of_gt hGapPos
  have hGap :=
    continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_gap_mul_total_le
      D variation hVariation hEdge M
  have hScaled :=
    mul_le_mul_of_nonneg_left hGap (inv_nonneg.mpr hGapPos.le)
  change
    continuousCompactOrientedGaugeWilsonTotalVariation w ≤
      (1 - D.coefficient)⁻¹ *
        continuousCompactOrientedGaugeWilsonTotalVariation variation
  calc
    continuousCompactOrientedGaugeWilsonTotalVariation w =
        (1 - D.coefficient)⁻¹ *
          ((1 - D.coefficient) *
            continuousCompactOrientedGaugeWilsonTotalVariation w) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ (1 - D.coefficient)⁻¹ *
        continuousCompactOrientedGaugeWilsonTotalVariation variation := hScaled

end

end MathlibAnalytic
end MGAP4D
