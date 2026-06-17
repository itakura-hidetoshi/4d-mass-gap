import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalVariationMinimality
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalRandomScanVariationContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual canonical link variation of the random-scan heat-bath sweep is
bounded by the declared Dobrushin-updated canonical profile. -/
theorem finite_lattice_canonicalLinkVariation_randomScanHeatBathSweep_le_updated
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (source : L.Edge) :
    L.canonicalLinkVariation (L.randomScanHeatBathSweep f) source ≤
      finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
        D (L.canonicalLinkVariation f) source := by
  simpa [finite_lattice_canonicalRandomScanHeatBathSweepVariationBound_variation]
    using
      (finite_lattice_canonicalLinkVariation_le_linkVariationBound
        L (L.randomScanHeatBathSweep f)
        (L.canonicalRandomScanHeatBathSweepVariationBound f D) source)

/-- The concrete random-scan heat-bath sweep contracts the actual total
canonical link variation at the standard Dobrushin random-scan rate. -/
theorem finite_lattice_canonical_randomScanHeatBathSweep_actual_totalVariation_le_rate_mul
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteLatticeWilsonTotalVariation
        (L.canonicalLinkVariation (L.randomScanHeatBathSweep f)) ≤
      finiteLatticeWilsonDobrushinRandomScanRate L D *
        finiteLatticeWilsonTotalVariation (L.canonicalLinkVariation f) := by
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
        finite_lattice_canonicalLinkVariation_randomScanHeatBathSweep_le_updated
          L f D source
    _ ≤ finiteLatticeWilsonDobrushinRandomScanRate L D *
        finiteLatticeWilsonTotalVariation (L.canonicalLinkVariation f) :=
      finite_lattice_canonical_randomScanHeatBathSweep_totalVariation_le_rate_mul
        L f D hEdge

end

end MathlibAnalytic
end MGAP4D
