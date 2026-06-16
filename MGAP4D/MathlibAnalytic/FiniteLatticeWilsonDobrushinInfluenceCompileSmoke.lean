import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinInfluence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {α : Type*} [Fintype α]
  (p q : PMF α)

example : 0 ≤ finitePMFTotalVariationReal p q :=
  finitePMFTotalVariationReal_nonneg p q

variable (L : FiniteLatticeWilsonSystem)
  (C : FiniteLatticeWilsonDobrushinInfluenceCertificate L)
  (hDecomposition :
    FiniteLatticeWilsonRandomScanVarianceDecompositionPrinciple L)
  (hComparison :
    FiniteLatticeWilsonDobrushinVarianceComparisonPrinciple L)

noncomputable def finite_lattice_dobrushin_to_random_scan_compile_smoke :
    FiniteLatticeWilsonRandomScanHeatBathContractionData L :=
  finiteLatticeWilsonRandomScanContractionDataOfDobrushin
    L C hDecomposition hComparison

example : L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_dobrushin
    L C hDecomposition hComparison

end

end MathlibAnalytic
end MGAP4D
