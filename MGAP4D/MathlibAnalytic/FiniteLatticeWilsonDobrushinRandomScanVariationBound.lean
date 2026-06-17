import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinRandomScanVariationContraction
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonRandomScanHeatBathSweep

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A centered link-variation profile for `f` induces a concrete link-variation
bound for the actual random-scan heat-bath observable.  Its declared profile is
the uniform average of the sharp single-target Dobrushin update profiles. -/
noncomputable def
    FiniteLatticeWilsonCenteredVariationProfile.randomScanHeatBathSweepVariationBound
    {L : FiniteLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteLatticeWilsonDobrushinMatrixData L) :
    FiniteLatticeWilsonLinkVariationBound L
      (L.randomScanHeatBathSweep f) := by
  classical
  refine
    { variation :=
        finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
          D P.variation
      variation_nonneg :=
        finite_lattice_dobrushinRandomScanUpdatedVariation_nonneg
          D P.variation P.variation_nonneg
      variation_bound := ?_ }
  intro source A B hAgree
  have hInvNonneg :
      0 ≤ (Fintype.card L.Edge : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hTarget
      (target : L.Edge) :
      |L.singleLinkConditionalExpectation f A target -
          L.singleLinkConditionalExpectation f B target| ≤
        finiteLatticeWilsonDobrushinUpdatedVariation
          D P.variation target source :=
    (P.conditionalExpectationVariationBound D target).variation_bound
      source A B hAgree
  have hSum :
      |∑ target : L.Edge,
          (L.singleLinkConditionalExpectation f A target -
            L.singleLinkConditionalExpectation f B target)| ≤
        ∑ target : L.Edge,
          finiteLatticeWilsonDobrushinUpdatedVariation
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
          finiteLatticeWilsonDobrushinUpdatedVariation
            D P.variation target source := by
        apply Finset.sum_le_sum
        intro target _htarget
        exact hTarget target
  rw [finite_lattice_randomScanHeatBathSweep_apply,
    finite_lattice_randomScanHeatBathSweep_apply]
  unfold finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
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
          finiteLatticeWilsonDobrushinUpdatedVariation
            D P.variation target source :=
      mul_le_mul_of_nonneg_left hSum hInvNonneg

/-- Direct pointwise variation estimate for the concrete random-scan Wilson
heat-bath sweep. -/
theorem finite_lattice_dobrushin_randomScanHeatBathSweep_difference_abs_le
    {L : FiniteLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source) :
    |L.randomScanHeatBathSweep f A -
        L.randomScanHeatBathSweep f B| ≤
      finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
        D P.variation source :=
  (P.randomScanHeatBathSweepVariationBound D).variation_bound
    source A B hAgree

/-- The concrete random-scan sweep therefore inherits the standard Dobrushin
contraction at the level of the declared total link-variation bound.  This is
still an oscillation-seminorm statement, not a Gibbs `L²` Rayleigh theorem. -/
theorem finite_lattice_dobrushin_randomScanHeatBathSweep_totalVariation_le_rate_mul
    {L : FiniteLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteLatticeWilsonTotalVariation
        (P.randomScanHeatBathSweepVariationBound D).variation ≤
      finiteLatticeWilsonDobrushinRandomScanRate L D *
        finiteLatticeWilsonTotalVariation P.variation := by
  change finiteLatticeWilsonTotalVariation
      (finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
        D P.variation) ≤
    finiteLatticeWilsonDobrushinRandomScanRate L D *
      finiteLatticeWilsonTotalVariation P.variation
  exact finite_lattice_dobrushinRandomScanUpdatedVariation_total_le_rate_mul
    D P.variation P.variation_nonneg hEdge

end

end MathlibAnalytic
end MGAP4D
