import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinInfluence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)
  (C : FiniteLatticeWilsonDobrushinInfluenceCertificate L)
  (hD : FiniteLatticeWilsonRandomScanVarianceDecompositionPrinciple L)
  (hC : FiniteLatticeWilsonDobrushinVarianceComparisonPrinciple L)

example : L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_dobrushin L C hD hC

end

end MathlibAnalytic
end MGAP4D
