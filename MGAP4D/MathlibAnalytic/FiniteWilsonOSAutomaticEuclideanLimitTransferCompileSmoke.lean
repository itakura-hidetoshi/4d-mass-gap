import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticEuclideanLimitTransfer

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

variable
  (W : FiniteWilsonOSAutomaticApproximationFamily)
  (D : FiniteWilsonOSAutomaticEuclideanLimitData W)

/-- Compile gate for conversion to the generic Euclidean-invariance limit
package. -/
noncomputable def finite_wilson_euclidean_limit_data_compile_smoke :
    EuclideanYangMillsEuclideanInvarianceLimitData :=
  D.toEuclideanInvarianceLimitData

/-- Compile gate for theorem-generated finite expectation equality. -/
theorem finite_wilson_finite_euclidean_invariance_compile_smoke
    (n : ℕ) (g : D.Transformation) (O : D.Observable) :
    D.toEuclideanInvarianceLimitData.finiteTransformedExpectation n g O =
      D.toEuclideanInvarianceLimitData.finiteReferenceExpectation n O :=
  D.toEuclideanInvarianceLimitData.finiteEuclideanInvariant n g O

/-- Compile gate for continuum Euclidean invariance. -/
theorem finite_wilson_continuum_euclidean_invariance_compile_smoke :
    D.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant :=
  finite_wilson_os_automatic_euclidean_invariance_passes_to_limit D

end

end MathlibAnalytic
end MGAP4D
