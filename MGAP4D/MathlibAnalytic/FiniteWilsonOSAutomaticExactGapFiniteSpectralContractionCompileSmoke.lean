import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapFiniteSpectralContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W)

noncomputable def finite_wilson_finite_spectral_positive_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapPositiveRayleighContractionData W :=
  D.toPositiveRayleighData

theorem finite_wilson_finite_spectral_operator_bound_compile_smoke
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_finite_spectral_data D n

theorem finite_wilson_finite_spectral_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_finite_spectral_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
