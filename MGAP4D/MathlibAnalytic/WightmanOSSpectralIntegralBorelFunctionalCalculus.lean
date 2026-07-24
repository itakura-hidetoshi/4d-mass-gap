import MGAP4D.MathlibAnalytic.WightmanOSBorelFunctionalCalculusEigenvectorEvaluation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure ExplicitWightmanOSRealSpectralIntegral
    (M : ExplicitWightmanOSReconstructedModel) where
  integral : (ℝ → ℝ) → M.H → M.H
  indicator_integral_eq_projection :
    ∀ (s : Set ℝ), MeasurableSet s → ∀ ψ : M.H,
      integral (s.indicator fun _ => (1 : ℝ)) ψ =
        M.spectralPVM.projection s ψ
  eigenvector_integral_evaluation :
    ∀ {E : ℝ} (x : M.hamiltonian.domain),
      M.hamiltonian x = E • (x : M.H) →
        ∀ f : ℝ → ℝ,
          integral f (x : M.H) = f E • (x : M.H)

def ExplicitWightmanOSRealSpectralIntegral.toBorelFunctionalCalculus
    {M : ExplicitWightmanOSReconstructedModel}
    (I : ExplicitWightmanOSRealSpectralIntegral M) :
    ExplicitWightmanOSRealBorelFunctionalCalculus M where
  apply := I.integral
  indicator_eq_projection := I.indicator_integral_eq_projection
  eigenvector_evaluation := I.eigenvector_integral_evaluation

theorem explicit_wightman_os_ambient_indicator_evaluation_of_spectralIntegral
    (M : ExplicitWightmanOSReconstructedModel)
    (I : ExplicitWightmanOSRealSpectralIntegral M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M := by
  exact explicit_wightman_os_ambient_indicator_evaluation_of_borelFunctionalCalculus
    M I.toBorelFunctionalCalculus

theorem explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_spectralIntegral
    (M : ExplicitWightmanOSReconstructedModel)
    (I : ExplicitWightmanOSRealSpectralIntegral M) :
    ExplicitWightmanOSAmbientEigenvectorOffEnergyIndicatorAnnihilationLaw M := by
  exact explicit_wightman_os_ambient_offEnergy_indicator_annihilation_of_borelFunctionalCalculus
    M I.toBorelFunctionalCalculus

theorem explicit_wightman_os_canonical_eigenprojection_law_of_spectralIntegral
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (I : ExplicitWightmanOSRealSpectralIntegral M) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M := by
  exact explicit_wightman_os_canonical_eigenprojection_law_of_borelFunctionalCalculus
    M P hQuadratic I.toBorelFunctionalCalculus

end

end MathlibAnalytic
end MGAP4D
