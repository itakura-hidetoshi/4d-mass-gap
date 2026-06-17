import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalRandomScanActualVariationContraction
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalTotalVariationDefiniteness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite Wilson random-scan heat-bath sweep contracts the exact canonical
total variation at the standard Dobrushin random-scan rate. -/
theorem finite_lattice_randomScanHeatBathSweep_canonicalTotalVariation_le_rate_mul
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalTotalVariation (L.randomScanHeatBathSweep f) ≤
      finiteLatticeWilsonDobrushinRandomScanRate L D *
        L.canonicalTotalVariation f := by
  unfold FiniteLatticeWilsonSystem.canonicalTotalVariation
  exact
    finite_lattice_canonical_randomScanHeatBathSweep_actual_totalVariation_le_rate_mul
      L f D hEdge

end

end MathlibAnalytic
end MGAP4D
