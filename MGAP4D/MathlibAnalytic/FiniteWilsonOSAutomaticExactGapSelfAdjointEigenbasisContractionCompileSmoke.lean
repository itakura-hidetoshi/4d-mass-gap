import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData W)

noncomputable def finite_wilson_self_adjoint_generated_basis_compile_smoke
    (n : ℕ) :
    OrthonormalBasis (Fin D.stateDimension) ℝ D.StateSpace :=
  D.generatedSpectralBasis n

noncomputable def finite_wilson_self_adjoint_orthonormal_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W :=
  D.toOrthonormalEigenbasisData

noncomputable def finite_wilson_self_adjoint_finite_spectral_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W :=
  D.toFiniteSpectralData

theorem finite_wilson_self_adjoint_operator_bound_compile_smoke
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_self_adjoint_eigenbasis D n

theorem finite_wilson_self_adjoint_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_self_adjoint_eigenbasis_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
