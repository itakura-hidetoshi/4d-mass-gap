import MGAP4D.MathlibAnalytic.WightmanOSEigenvectorComplementSpectralLocalization
import MGAP4D.MathlibAnalytic.WightmanOSCountablyAdditivePVMScalarMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Zero scalar spectral mass on a measurable set forces the corresponding PVM
projection of the vector to vanish. -/
theorem countably_additive_pvm_projection_zero_of_scalarMeasure_zero
    {M : ExplicitWightmanOSReconstructedModel}
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (ψ : M.H) (s : Set ℝ) (hs : MeasurableSet s)
    (hMass : (P.scalarMeasure ψ).real s = 0) :
    M.spectralPVM.projection s ψ = 0 := by
  rw [P.scalarMeasure_real_eq_projectionNormSq ψ s hs] at hMass
  have hNorm : ‖M.spectralPVM.projection s ψ‖ = 0 := by
    nlinarith [norm_nonneg (M.spectralPVM.projection s ψ)]
  exact norm_eq_zero.mp hNorm

/-- Scalar-measure localization at ambient Hamiltonian eigenvectors: the scalar
spectral measure of an eigenvector has zero mass outside its eigenvalue. -/
def ExplicitWightmanOSAmbientEigenvectorScalarMeasureLocalizationLaw
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M) : Prop :=
  ∀ {E : ℝ} (x : M.hamiltonian.domain),
    M.hamiltonian x = E • (x : M.H) →
      (P.scalarMeasure (x : M.H)).real (({E} : Set ℝ)ᶜ) = 0

/-- Scalar-measure localization implies the ambient complement-annihilation law
through the measurable-set quadratic PVM identity. -/
theorem explicit_wightman_os_ambient_complement_annihilation_of_scalarMeasure_localization
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hLocalization :
      ExplicitWightmanOSAmbientEigenvectorScalarMeasureLocalizationLaw M P) :
    ExplicitWightmanOSAmbientEigenvectorComplementAnnihilationLaw M := by
  intro E x hEigen
  exact countably_additive_pvm_projection_zero_of_scalarMeasure_zero
    P (x : M.H) (({E} : Set ℝ)ᶜ) (MeasurableSet.singleton E).compl
      (hLocalization x hEigen)

/-- Scalar-measure localization therefore yields the ambient singleton
spectral projection law. -/
theorem explicit_wightman_os_ambient_eigenprojection_law_of_scalarMeasure_localization
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hLocalization :
      ExplicitWightmanOSAmbientEigenvectorScalarMeasureLocalizationLaw M P) :
    ExplicitWightmanOSAmbientEigenprojectionLaw M := by
  exact explicit_wightman_os_ambient_eigenprojection_law_of_complement M
    (explicit_wightman_os_ambient_complement_annihilation_of_scalarMeasure_localization
      M P hLocalization)

/-- Scalar-measure localization also yields the canonical vacuum-orthogonal
singleton eigenprojection law. -/
theorem explicit_wightman_os_canonical_eigenprojection_law_of_scalarMeasure_localization
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hLocalization :
      ExplicitWightmanOSAmbientEigenvectorScalarMeasureLocalizationLaw M P) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M := by
  exact explicit_wightman_os_canonical_eigenprojection_law_of_ambient M
    (explicit_wightman_os_ambient_eigenprojection_law_of_scalarMeasure_localization
      M P hLocalization)

end

end MathlibAnalytic
end MGAP4D
