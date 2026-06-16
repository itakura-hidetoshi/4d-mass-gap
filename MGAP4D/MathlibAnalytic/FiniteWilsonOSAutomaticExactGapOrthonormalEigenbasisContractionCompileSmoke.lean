import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W)

noncomputable def finite_wilson_orthonormal_eigenbasis_finite_spectral_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W :=
  D.toFiniteSpectralData

theorem finite_wilson_orthonormal_eigenbasis_weight_sum_compile_smoke
    (n : ℕ) (x : D.StateSpace) :
    ∑ i : D.SpectralIndex n,
        (inner ℝ (D.spectralBasis n i) x) ^ 2 = ‖x‖ ^ 2 :=
  finite_wilson_orthonormal_eigenbasis_weight_sum D n x

theorem finite_wilson_orthonormal_eigenbasis_operator_bound_compile_smoke
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_orthonormal_eigenbasis D n

theorem finite_wilson_orthonormal_eigenbasis_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_orthonormal_eigenbasis_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
