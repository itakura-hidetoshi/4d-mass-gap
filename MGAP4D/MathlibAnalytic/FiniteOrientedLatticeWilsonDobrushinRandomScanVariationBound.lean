import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinRandomScanVariationContraction
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonRandomScanHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

noncomputable def
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanHeatBathSweepVariationBound
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) :
    FiniteOrientedLatticeWilsonLinkVariationBound L
      (L.randomScanHeatBathSweep f) := by
  classical
  refine
    { variation :=
        finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
          D P.variation
      variation_nonneg :=
        finite_oriented_dobrushinRandomScanUpdatedVariation_nonneg
          D P.variation P.variation_nonneg
      variation_bound := ?_ }
  intro source A B hAgree
  have hInvNonneg :
      0 ≤ (Fintype.card L.Edge : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hTarget (target : L.Edge) :
      |L.singleLinkConditionalExpectation f A target -
          L.singleLinkConditionalExpectation f B target| ≤
        finiteOrientedLatticeWilsonDobrushinUpdatedVariation
          D P.variation target source :=
    (P.conditionalExpectationVariationBound D target).variation_bound
      source A B hAgree
  have hSum :
      |∑ target : L.Edge,
          (L.singleLinkConditionalExpectation f A target -
            L.singleLinkConditionalExpectation f B target)| ≤
        ∑ target : L.Edge,
          finiteOrientedLatticeWilsonDobrushinUpdatedVariation
            D P.variation target source := by
    calc
      |∑ target : L.Edge,
          (L.singleLinkConditionalExpectation f A target -
            L.singleLinkConditionalExpectation f B target)| ≤
        ∑ target : L.Edge,
          |L.singleLinkConditionalExpectation f A target -
            L.singleLinkConditionalExpectation f B target| :=
        finite_abs_sum_le_sum_abs Finset.univ
          (fun target : L.Edge =>
            L.singleLinkConditionalExpectation f A target -
              L.singleLinkConditionalExpectation f B target)
      _ ≤ ∑ target : L.Edge,
          finiteOrientedLatticeWilsonDobrushinUpdatedVariation
            D P.variation target source := by
        apply Finset.sum_le_sum
        intro target _htarget
        exact hTarget target
  rw [finite_oriented_randomScanHeatBathSweep_apply,
    finite_oriented_randomScanHeatBathSweep_apply]
  unfold finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
  calc
    |(Fintype.card L.Edge : ℝ)⁻¹ *
          (∑ target : L.Edge,
            L.singleLinkConditionalExpectation f A target) -
        (Fintype.card L.Edge : ℝ)⁻¹ *
          (∑ target : L.Edge,
            L.singleLinkConditionalExpectation f B target)| =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        |∑ target : L.Edge,
          (L.singleLinkConditionalExpectation f A target -
            L.singleLinkConditionalExpectation f B target)| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg hInvNonneg]
    _ ≤ (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ target : L.Edge,
          finiteOrientedLatticeWilsonDobrushinUpdatedVariation
            D P.variation target source :=
      mul_le_mul_of_nonneg_left hSum hInvNonneg

theorem finite_oriented_dobrushin_randomScanHeatBathSweep_totalVariation_le_rate_mul
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteOrientedLatticeWilsonTotalVariation
        (P.randomScanHeatBathSweepVariationBound D).variation ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanRate L D *
        finiteOrientedLatticeWilsonTotalVariation P.variation := by
  change finiteOrientedLatticeWilsonTotalVariation
      (finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
        D P.variation) ≤
    finiteOrientedLatticeWilsonDobrushinRandomScanRate L D *
      finiteOrientedLatticeWilsonTotalVariation P.variation
  exact finite_oriented_dobrushinRandomScanUpdatedVariation_total_le_rate_mul
    D P.variation P.variation_nonneg hEdge

end
end MathlibAnalytic
end MGAP4D
