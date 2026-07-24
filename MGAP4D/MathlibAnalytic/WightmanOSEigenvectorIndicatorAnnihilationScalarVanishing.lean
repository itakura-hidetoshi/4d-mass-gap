import MGAP4D.MathlibAnalytic.WightmanOSEigenvectorOffEnergyScalarVanishing

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Exact ENNReal-valued quadratic realization of the scalar spectral measure on
measurable sets.  This strengthens the existing `.real` identity precisely enough
to exclude an artificial infinite-mass branch. -/
def ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M) : Prop :=
  ∀ (ψ : M.H) (s : Set ℝ), MeasurableSet s →
    P.scalarMeasure ψ s =
      ENNReal.ofReal (‖M.spectralPVM.projection s ψ‖ ^ 2)

/-- Indicator functional-calculus annihilation away from an ambient Hamiltonian
eigenvalue: every measurable spectral projection disjoint from the eigenvalue
kills the corresponding eigenvector. -/
def ExplicitWightmanOSAmbientEigenvectorOffEnergyIndicatorAnnihilationLaw
    (M : ExplicitWightmanOSReconstructedModel) : Prop :=
  ∀ {E : ℝ} (x : M.hamiltonian.domain),
    M.hamiltonian x = E • (x : M.H) →
      ∀ (s : Set ℝ), MeasurableSet s → Disjoint s ({E} : Set ℝ) →
        M.spectralPVM.projection s (x : M.H) = 0

/-- Exact ENNReal quadratic realization turns off-energy indicator annihilation
into off-energy scalar spectral vanishing. -/
theorem explicit_wightman_os_ambient_offEnergy_scalar_vanishing_of_indicator_annihilation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hIndicator :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyIndicatorAnnihilationLaw M) :
    ExplicitWightmanOSAmbientEigenvectorOffEnergyScalarVanishingLaw M P := by
  intro E x hEigen s hs hDisjoint
  rw [hQuadratic (x : M.H) s hs, hIndicator x hEigen s hs hDisjoint]
  simp

/-- Indicator annihilation and exact ENNReal quadratic realization imply zero
restriction of the scalar spectral measure away from every eigenvalue. -/
theorem explicit_wightman_os_ambient_scalarMeasure_restriction_of_indicator_annihilation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hIndicator :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyIndicatorAnnihilationLaw M) :
    ExplicitWightmanOSAmbientEigenvectorScalarMeasureRestrictionLaw M P := by
  exact explicit_wightman_os_ambient_scalarMeasure_restriction_of_offEnergy_vanishing
    M P
      (explicit_wightman_os_ambient_offEnergy_scalar_vanishing_of_indicator_annihilation
        M P hQuadratic hIndicator)

/-- Indicator annihilation and exact ENNReal quadratic realization imply ambient
complement annihilation. -/
theorem explicit_wightman_os_ambient_complement_annihilation_of_indicator_annihilation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hIndicator :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyIndicatorAnnihilationLaw M) :
    ExplicitWightmanOSAmbientEigenvectorComplementAnnihilationLaw M := by
  exact explicit_wightman_os_ambient_complement_annihilation_of_offEnergy_vanishing
    M P
      (explicit_wightman_os_ambient_offEnergy_scalar_vanishing_of_indicator_annihilation
        M P hQuadratic hIndicator)

/-- Indicator annihilation and exact ENNReal quadratic realization imply the
ambient singleton eigenprojection law. -/
theorem explicit_wightman_os_ambient_eigenprojection_law_of_indicator_annihilation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hIndicator :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyIndicatorAnnihilationLaw M) :
    ExplicitWightmanOSAmbientEigenprojectionLaw M := by
  exact explicit_wightman_os_ambient_eigenprojection_law_of_offEnergy_vanishing
    M P
      (explicit_wightman_os_ambient_offEnergy_scalar_vanishing_of_indicator_annihilation
        M P hQuadratic hIndicator)

/-- Indicator annihilation and exact ENNReal quadratic realization also imply the
canonical vacuum-orthogonal singleton eigenprojection law. -/
theorem explicit_wightman_os_canonical_eigenprojection_law_of_indicator_annihilation
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hQuadratic : ExplicitWightmanOSScalarMeasureENNRealQuadraticLaw M P)
    (hIndicator :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyIndicatorAnnihilationLaw M) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M := by
  exact explicit_wightman_os_canonical_eigenprojection_law_of_offEnergy_vanishing
    M P
      (explicit_wightman_os_ambient_offEnergy_scalar_vanishing_of_indicator_annihilation
        M P hQuadratic hIndicator)

end

end MathlibAnalytic
end MGAP4D
