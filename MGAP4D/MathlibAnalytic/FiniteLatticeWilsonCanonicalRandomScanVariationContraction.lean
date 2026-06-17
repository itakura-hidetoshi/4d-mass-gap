import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalCenteredVariationProfile
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinRandomScanVariationBound

namespace MGAP4D
namespace MathlibAnalytic

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

/-- Every finite Wilson observable therefore inherits the standard Dobrushin
random-scan contraction in canonical total link variation.  This remains a
finite oscillation-seminorm result, not a Gibbs `L²` Rayleigh theorem. -/
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

end

end MathlibAnalytic
end MGAP4D
