import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinInfluence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)
  (C : FiniteLatticeWilsonDobrushinInfluenceCertificate L)
  (hDecomposition : FiniteLatticeWilsonRandomScanVarianceDecompositionPrinciple L)
  (hComparison : FiniteLatticeWilsonDobrushinVarianceComparisonPrinciple L)

example : L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_dobrushin
    L C hDecomposition hComparison

end

end MathlibAnalytic
end MGAP4D
