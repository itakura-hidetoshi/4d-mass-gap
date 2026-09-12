import MGAP4D.MathlibAnalytic.WightmanOSSpectralIntegralBorelFunctionalCalculus
import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHilbertReconstructedModel

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Spectral-integral data specialized to the actual OS physical-Hilbert
reconstructed Yang--Mills model.  The Hamiltonian self-adjointness proof is not an
extra assumption: it is inherited from the reconstructed model itself. -/
structure EuclideanYangMillsOSPhysicalSpectralIntegral
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) where
  integral : (ℝ → ℝ) → M.toExplicitModel.H → M.toExplicitModel.H
  indicator_integral_eq_projection :
    ∀ (s : Set ℝ), MeasurableSet s → ∀ ψ : M.toExplicitModel.H,
      integral (s.indicator fun _ => (1 : ℝ)) ψ =
        M.toExplicitModel.spectralPVM.projection s ψ
  eigenvector_integral_evaluation :
    ∀ {E : ℝ} (x : M.toExplicitModel.hamiltonian.domain),
      M.toExplicitModel.hamiltonian x = E • (x : M.toExplicitModel.H) →
        ∀ f : ℝ → ℝ,
          integral f (x : M.toExplicitModel.H) =
            f E • (x : M.toExplicitModel.H)

/-- The actual OS reconstructed model already supplies the required
self-adjointness certificate. -/
theorem euclidean_yang_mills_os_physical_spectralIntegral_hamiltonian_selfAdjoint
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    IsSelfAdjoint M.toExplicitModel.hamiltonian :=
  M.toExplicitModel.hamiltonianSelfAdjoint

/-- Forget the model-specific wrapper and obtain the generic real spectral
integral used by the functional-calculus chain. -/
def EuclideanYangMillsOSPhysicalSpectralIntegral.toRealSpectralIntegral
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (I : EuclideanYangMillsOSPhysicalSpectralIntegral M) :
    ExplicitWightmanOSRealSpectralIntegral M.toExplicitModel where
  integral := I.integral
  indicator_integral_eq_projection := I.indicator_integral_eq_projection
  eigenvector_integral_evaluation := I.eigenvector_integral_evaluation

/-- Actual OS physical spectral integration yields the ambient measurable-set
indicator evaluation law. -/
theorem euclidean_yang_mills_os_physical_ambient_indicator_evaluation_of_spectralIntegral
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (I : EuclideanYangMillsOSPhysicalSpectralIntegral M) :
    ExplicitWightmanOSAmbientEigenvectorIndicatorEvaluationLaw M.toExplicitModel := by
  exact explicit_wightman_os_ambient_indicator_evaluation_of_spectralIntegral
    M.toExplicitModel I.toRealSpectralIntegral

/-- Together with exact scalar-measure quadratic realization, the actual OS
physical spectral integral yields canonical singleton eigenprojection
compatibility. -/
theorem euclidean_yang_mills_os_physical_canonical_eigenprojection_law_of_spectralIntegral
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M.toExplicitModel)
    (hQuadratic :
      ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M.toExplicitModel P)
    (I : EuclideanYangMillsOSPhysicalSpectralIntegral M) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M.toExplicitModel := by
  exact explicit_wightman_os_canonical_eigenprojection_law_of_spectralIntegral
    M.toExplicitModel P hQuadratic I.toRealSpectralIntegral

end

end MathlibAnalytic
end MGAP4D
