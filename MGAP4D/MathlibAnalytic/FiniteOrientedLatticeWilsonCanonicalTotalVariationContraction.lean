import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalRandomScanVariationContraction
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalTotalVariationHomogeneity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem finite_oriented_randomScanHeatBathSweep_canonicalTotalVariation_le_rate_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalTotalVariation (L.randomScanHeatBathSweep f) ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanRate L D *
        L.canonicalTotalVariation f := by
  simpa [FiniteOrientedLatticeWilsonSystem.canonicalTotalVariation] using
    (finite_oriented_canonical_randomScanHeatBathSweep_actualTotalVariation_le_rate_mul
      L f D hEdge)

end
end MathlibAnalytic
end MGAP4D
