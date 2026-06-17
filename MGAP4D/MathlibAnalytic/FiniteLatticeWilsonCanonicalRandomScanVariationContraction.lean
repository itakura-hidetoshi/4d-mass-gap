import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalVariationMinimality
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinRandomScanVariationBound

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The variation field of the canonical centered profile is exactly the
canonical global single-link fiber range. -/
@[simp] theorem finite_lattice_canonicalCenteredVariationProfile_variation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    (L.canonicalCenteredVariationProfile f).variation =
      L.canonicalLinkVariation f := by
  rfl

/-- The concrete random-scan heat-bath sweep of an arbitrary finite Wilson
observable carries the link-variation bound induced by its canonical centered
profile. -/
noncomputable def
    FiniteLatticeWilsonSystem.canonicalRandomScanHeatBathSweepVariationBound
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L) :
    FiniteLatticeWilsonLinkVariationBound L
      (L.randomScanHeatBathSweep f) :=
  FiniteLatticeWilsonCenteredVariationProfile.randomScanHeatBathSweepVariationBound
    (L.canonicalCenteredVariationProfile f) D

/-- The declared canonical random-scan variation is the standard averaged
Dobrushin update of the canonical link variation. -/
@[simp] theorem
    finite_lattice_canonicalRandomScanHeatBathSweepVariationBound_variation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L) :
    (L.canonicalRandomScanHeatBathSweepVariationBound f D).variation =
      finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
        D (L.canonicalLinkVariation f) := by
  rfl

/-- Pointwise one-link oscillation estimate for the concrete random-scan sweep
of an arbitrary finite Wilson observable, with no externally supplied variation
profile. -/
theorem finite_lattice_canonical_randomScanHeatBathSweep_difference_abs_le
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source) :
    |L.randomScanHeatBathSweep f A -
        L.randomScanHeatBathSweep f B| ≤
      finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
        D (L.canonicalLinkVariation f) source := by
  exact
    (L.canonicalRandomScanHeatBathSweepVariationBound f D).variation_bound
      source A B hAgree

/-- The actual canonical variation of the random-scan sweep lies below its
proof-relevant Dobrushin update profile. -/
theorem
    finite_lattice_canonical_randomScanHeatBathSweep_canonicalVariation_le_updatedVariation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (source : L.Edge) :
    L.canonicalLinkVariation (L.randomScanHeatBathSweep f) source ≤
      finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
        D (L.canonicalLinkVariation f) source := by
  exact finite_lattice_canonicalLinkVariation_le_linkVariationBound
    L (L.randomScanHeatBathSweep f)
      (L.canonicalRandomScanHeatBathSweepVariationBound f D) source

/-- The declared updated profile satisfies the standard Dobrushin total
variation contraction. -/
theorem finite_lattice_canonical_randomScanHeatBathSweep_totalVariation_le_rate_mul
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteLatticeWilsonTotalVariation
        (finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
          D (L.canonicalLinkVariation f)) ≤
      finiteLatticeWilsonDobrushinRandomScanRate L D *
        finiteLatticeWilsonTotalVariation
          (L.canonicalLinkVariation f) := by
  simpa using
    (finite_lattice_dobrushin_randomScanHeatBathSweep_totalVariation_le_rate_mul
      (L.canonicalCenteredVariationProfile f) D hEdge)

/-- The concrete random-scan heat-bath sweep contracts its actual canonical
total link variation at the certified Dobrushin rate.  This is a genuine
oscillation-seminorm statement for the updated observable, not merely for a
declared upper-bound profile. -/
theorem
    finite_lattice_canonical_randomScanHeatBathSweep_actualTotalVariation_le_rate_mul
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteLatticeWilsonTotalVariation
        (L.canonicalLinkVariation (L.randomScanHeatBathSweep f)) ≤
      finiteLatticeWilsonDobrushinRandomScanRate L D *
        finiteLatticeWilsonTotalVariation
          (L.canonicalLinkVariation f) := by
  calc
    finiteLatticeWilsonTotalVariation
        (L.canonicalLinkVariation (L.randomScanHeatBathSweep f)) ≤
      finiteLatticeWilsonTotalVariation
        (finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
          D (L.canonicalLinkVariation f)) := by
      unfold finiteLatticeWilsonTotalVariation
      apply Finset.sum_le_sum
      intro source _hsource
      exact
        finite_lattice_canonical_randomScanHeatBathSweep_canonicalVariation_le_updatedVariation
          L f D source
    _ ≤ finiteLatticeWilsonDobrushinRandomScanRate L D *
        finiteLatticeWilsonTotalVariation
          (L.canonicalLinkVariation f) :=
      finite_lattice_canonical_randomScanHeatBathSweep_totalVariation_le_rate_mul
        L f D hEdge

end

end MathlibAnalytic
end MGAP4D
