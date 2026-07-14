import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Pointwise uniform random-scan average of exact compact-Haar one-link
conditional expectations on bounded continuous observables. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanConditionalExpectationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) : ℝ :=
  (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
    ∑ target : C.base.geometry.Edge,
      C.singleLinkConditionalExpectationBCF O A target

/-- Finite total link variation of a compact-Haar observable profile. -/
def continuousCompactOrientedGaugeWilsonTotalVariation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (variation : C.base.geometry.Edge → ℝ) : ℝ :=
  ∑ source : C.base.geometry.Edge, variation source

/-- Exact variation profile after uniformly averaging all sharp one-target
Dobrushin updates. -/
noncomputable def
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (source : C.base.geometry.Edge) : ℝ :=
  (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
    ∑ target : C.base.geometry.Edge,
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D variation target source

/-- A nonnegative variation profile remains nonnegative after compact-Haar
random-scan averaging. -/
theorem continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_nonneg
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e, 0 ≤ variation e)
    (source : C.base.geometry.Edge) :
    0 ≤ continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
      D variation source := by
  unfold continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun target _ =>
      continuous_compact_oriented_dobrushinUpdatedVariation_nonneg
        D variation hVariation target source)

/-- Exact finite-sum expression for one sharp target-link variation update. -/
theorem continuous_compact_oriented_dobrushinUpdatedVariation_sum_eq
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (target : C.base.geometry.Edge) :
    (∑ source,
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D variation target source) =
      (∑ source, variation source) +
        (∑ source, D.influence target source) * variation target -
          variation target := by
  classical
  have hPointwise (source : C.base.geometry.Edge) :
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source =
        variation source + D.influence target source * variation target -
          (if source = target then variation target else 0) := by
    by_cases h : source = target
    · subst source
      simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation,
        D.influence_diagonal_zero]
    · simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation, h]
  calc
    (∑ source,
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D variation target source) =
      ∑ source,
        (variation source + D.influence target source * variation target -
          (if source = target then variation target else 0)) := by
      apply Finset.sum_congr rfl
      intro source _
      exact hPointwise source
    _ = (∑ source, variation source) +
        (∑ source, D.influence target source) * variation target -
          variation target := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
      simp

/-- One exact target-link update decreases total link variation by at least
`(1 - coefficient) * variation target`. -/
theorem continuous_compact_oriented_dobrushinUpdatedVariation_total_le
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e, 0 ≤ variation e)
    (target : C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        (continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target) ≤
      continuousCompactOrientedGaugeWilsonTotalVariation variation -
        (1 - D.coefficient) * variation target := by
  have hRowMul :
      (∑ source, D.influence target source) * variation target ≤
        D.coefficient * variation target :=
    mul_le_mul_of_nonneg_right
      (D.rowSum_le_coefficient target) (hVariation target)
  unfold continuousCompactOrientedGaugeWilsonTotalVariation
  rw [continuous_compact_oriented_dobrushinUpdatedVariation_sum_eq]
  calc
    (∑ source, variation source) +
          (∑ source, D.influence target source) * variation target -
            variation target ≤
      (∑ source, variation source) +
          D.coefficient * variation target - variation target :=
      sub_le_sub_right (add_le_add (le_refl _) hRowMul) _
    _ = (∑ source, variation source) -
        (1 - D.coefficient) * variation target := by ring

/-- Summing the averaged profile over source links is the normalized average of
all one-target total variations. -/
theorem continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_total_eq
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
          D variation) =
      (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
        ∑ target,
          continuousCompactOrientedGaugeWilsonTotalVariation
            (continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
              D variation target) := by
  classical
  unfold continuousCompactOrientedGaugeWilsonTotalVariation
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- Compact-Haar random-scan averaging contracts total link variation at the
standard Dobrushin rate `1 - (1 - coefficient) / |Edge|`. -/
theorem continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_total_le_rate_mul
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
          D variation) ≤
      continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
        continuousCompactOrientedGaugeWilsonTotalVariation variation := by
  let n : ℝ := Fintype.card C.base.geometry.Edge
  let total : ℝ :=
    continuousCompactOrientedGaugeWilsonTotalVariation variation
  let gap : ℝ := 1 - D.coefficient
  have hCardPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hCardNe : n ≠ 0 := ne_of_gt hCardPos
  have hInvNonneg : 0 ≤ n⁻¹ := inv_nonneg.mpr hCardPos.le
  have hTargetSum :
      (∑ target,
        continuousCompactOrientedGaugeWilsonTotalVariation
          (continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
            D variation target)) ≤
      ∑ target, (total - gap * variation target) := by
    apply Finset.sum_le_sum
    intro target _
    exact continuous_compact_oriented_dobrushinUpdatedVariation_total_le
      D variation hVariation target
  have hConstSum : (∑ _target : C.base.geometry.Edge, total) = n * total := by
    simp [n, nsmul_eq_mul]
  have hDropSum :
      (∑ target, gap * variation target) = gap * total := by
    unfold total continuousCompactOrientedGaugeWilsonTotalVariation
    rw [← Finset.mul_sum]
  rw [continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_total_eq]
  change n⁻¹ *
      (∑ target,
        continuousCompactOrientedGaugeWilsonTotalVariation
          (continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
            D variation target)) ≤
    continuousCompactOrientedDobrushinRandomScanRate C D.coefficient * total
  calc
    n⁻¹ *
        (∑ target,
          continuousCompactOrientedGaugeWilsonTotalVariation
            (continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
              D variation target)) ≤
      n⁻¹ * ∑ target, (total - gap * variation target) :=
      mul_le_mul_of_nonneg_left hTargetSum hInvNonneg
    _ = n⁻¹ * (n * total - gap * total) := by
      rw [Finset.sum_sub_distrib, hConstSum, hDropSum]
    _ = continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
        total := by
      dsimp [n, gap]
      unfold continuousCompactOrientedDobrushinRandomScanRate
      field_simp [hCardNe]

/-- A centered bounded-observable profile induces a concrete variation bound
for the actual compact-Haar random-scan conditional expectation. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.randomScanVariationBound
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (C.randomScanConditionalExpectationBCF O) := by
  classical
  refine
    { variation :=
        continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
          D P.variation
      variation_nonneg :=
        continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_nonneg
          D P.variation P.variation_nonneg
      variation_bound := ?_ }
  intro source A B hAgree
  have hInvNonneg :
      0 ≤ (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hTarget (target : C.base.geometry.Edge) :
      |C.singleLinkConditionalExpectationBCF O A target -
          C.singleLinkConditionalExpectationBCF O B target| ≤
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D P.variation target source :=
    (P.conditionalExpectationVariationBound D target).variation_bound
      source A B hAgree
  have hSum :
      |∑ target,
          (C.singleLinkConditionalExpectationBCF O A target -
            C.singleLinkConditionalExpectationBCF O B target)| ≤
        ∑ target,
          continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
            D P.variation target source := by
    calc
      |∑ target,
          (C.singleLinkConditionalExpectationBCF O A target -
            C.singleLinkConditionalExpectationBCF O B target)| ≤
        ∑ target,
          |C.singleLinkConditionalExpectationBCF O A target -
            C.singleLinkConditionalExpectationBCF O B target| :=
        finite_abs_sum_le_sum_abs Finset.univ _
      _ ≤ ∑ target,
          continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
            D P.variation target source := by
        apply Finset.sum_le_sum
        intro target _
        exact hTarget target
  unfold ContinuousCompactOrientedGaugeWilsonSystem.randomScanConditionalExpectationBCF
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
  calc
    |(Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
          (∑ target, C.singleLinkConditionalExpectationBCF O A target) -
        (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
          (∑ target, C.singleLinkConditionalExpectationBCF O B target)| =
      (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
        |∑ target,
          (C.singleLinkConditionalExpectationBCF O A target -
            C.singleLinkConditionalExpectationBCF O B target)| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg hInvNonneg]
    _ ≤ (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
        ∑ target,
          continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
            D P.variation target source :=
      mul_le_mul_of_nonneg_left hSum hInvNonneg

/-- Direct pointwise random-scan variation estimate for a bounded continuous
compact-Haar observable. -/
theorem continuous_compact_oriented_dobrushin_randomScanConditionalExpectationBCF_difference_abs_le
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (source : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B source) :
    |C.randomScanConditionalExpectationBCF O A -
        C.randomScanConditionalExpectationBCF O B| ≤
      continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
        D P.variation source :=
  (P.randomScanVariationBound D).variation_bound source A B hAgree

/-- The declared observable random-scan profile contracts in total variation at
the certified compact Dobrushin random-scan rate. -/
theorem continuous_compact_oriented_dobrushin_randomScanVariation_total_le_rate_mul
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        (P.randomScanVariationBound D).variation ≤
      continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
        continuousCompactOrientedGaugeWilsonTotalVariation P.variation := by
  change continuousCompactOrientedGaugeWilsonTotalVariation
      (continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
        D P.variation) ≤
    continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
      continuousCompactOrientedGaugeWilsonTotalVariation P.variation
  exact
    continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_total_le_rate_mul
      D P.variation P.variation_nonneg hEdge

end

end MathlibAnalytic
end MGAP4D
