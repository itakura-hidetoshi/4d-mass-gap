import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticEuclideanFiniteSymmetry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable
  (L : FiniteLatticeWilsonSystem)
  (E : FiniteLatticeWilsonEuclideanSymmetryCertificate L)

/-- Compile gate for pointwise Wilson Gibbs PMF invariance. -/
theorem finite_wilson_gibbs_pmf_euclidean_compile_smoke
    (g : E.Transformation) (A : L.Configuration) :
    L.gibbsPMF (E.configurationEquiv g A) = L.gibbsPMF A :=
  finite_lattice_gibbsPMF_euclideanInvariant E g A

/-- Compile gate for finite Wilson Gibbs expectation invariance. -/
theorem finite_wilson_gibbs_expectation_euclidean_compile_smoke
    (g : E.Transformation) (O : L.Configuration → ℝ) :
    E.transformedGibbsExpectation g O = L.gibbsExpectation O :=
  finite_lattice_gibbsExpectation_euclideanInvariant E g O

end

end MathlibAnalytic
end MGAP4D
