import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalVariationMinimality
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinRandomScanVariationBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

@[simp] theorem finite_oriented_canonicalCenteredVariationProfile_variation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    (L.canonicalCenteredVariationProfile f).variation =
      L.canonicalLinkVariation f := by
  rfl

noncomputable def
    FiniteOrientedLatticeWilsonSystem.canonicalRandomScanHeatBathSweepVariationBound
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) :
    FiniteOrientedLatticeWilsonLinkVariationBound L
      (L.randomScanHeatBathSweep f) :=
  FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanHeatBathSweepVariationBound
    (L.canonicalCenteredVariationProfile f) D

@[simp] theorem
    finite_oriented_canonicalRandomScanHeatBathSweepVariationBound_variation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) :
    (L.canonicalRandomScanHeatBathSweepVariationBound f D).variation =
      finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
        D (L.canonicalLinkVariation f) := by
  rfl

theorem finite_oriented_canonical_randomScanHeatBathSweep_canonicalVariation_le_updatedVariation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (source : L.Edge) :
    L.canonicalLinkVariation (L.randomScanHeatBathSweep f) source ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
        D (L.canonicalLinkVariation f) source := by
  exact finite_oriented_canonicalLinkVariation_le_linkVariationBound
    L (L.randomScanHeatBathSweep f)
      (L.canonicalRandomScanHeatBathSweepVariationBound f D) source

theorem finite_oriented_canonical_randomScanHeatBathSweep_actualTotalVariation_le_rate_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteOrientedLatticeWilsonTotalVariation
        (L.canonicalLinkVariation (L.randomScanHeatBathSweep f)) ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanRate L D *
        finiteOrientedLatticeWilsonTotalVariation
          (L.canonicalLinkVariation f) := by
  calc
    finiteOrientedLatticeWilsonTotalVariation
        (L.canonicalLinkVariation (L.randomScanHeatBathSweep f)) ≤
      finiteOrientedLatticeWilsonTotalVariation
        (finiteOrientedLatticeWilsonDobrushinRandomScanUpdatedVariation
          D (L.canonicalLinkVariation f)) := by
      unfold finiteOrientedLatticeWilsonTotalVariation
      apply Finset.sum_le_sum
      intro source _hsource
      exact
        finite_oriented_canonical_randomScanHeatBathSweep_canonicalVariation_le_updatedVariation
          L f D source
    _ ≤ finiteOrientedLatticeWilsonDobrushinRandomScanRate L D *
        finiteOrientedLatticeWilsonTotalVariation
          (L.canonicalLinkVariation f) :=
      finite_oriented_dobrushinRandomScanUpdatedVariation_total_le_rate_mul
        D (L.canonicalLinkVariation f)
          (finite_oriented_canonicalLinkVariation_nonneg L f) hEdge

end
end MathlibAnalytic
end MGAP4D
