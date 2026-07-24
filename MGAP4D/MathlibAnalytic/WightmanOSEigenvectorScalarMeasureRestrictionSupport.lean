import MGAP4D.MathlibAnalytic.WightmanOSEigenvectorScalarMeasureLocalization

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Support-level scalar spectral localization for ambient Hamiltonian eigenvectors:
the scalar spectral measure restricted away from the eigenvalue is the zero
measure.  This packages vanishing on every measurable subset of the complement,
rather than only its total real-valued mass. -/
def ExplicitWightmanOSAmbientEigenvectorScalarMeasureRestrictionLaw
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M) : Prop :=
  ∀ {E : ℝ} (x : M.hamiltonian.domain),
    M.hamiltonian x = E • (x : M.H) →
      (P.scalarMeasure (x : M.H)).restrict (({E} : Set ℝ)ᶜ) = 0

/-- A zero restriction to the complement of an eigenvalue implies zero scalar
mass on that complement. -/
theorem explicit_wightman_os_ambient_scalarMeasure_localization_of_restriction
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hRestriction :
      ExplicitWightmanOSAmbientEigenvectorScalarMeasureRestrictionLaw M P) :
    ExplicitWightmanOSAmbientEigenvectorScalarMeasureLocalizationLaw M P := by
  intro E x hEigen
  have hMeasure := congrArg
    (fun μ : Measure ℝ => μ (({E} : Set ℝ)ᶜ))
    (hRestriction x hEigen)
  rw [Measure.restrict_apply (MeasurableSet.singleton E).compl] at hMeasure
  change (P.scalarMeasure (x : M.H) (({E} : Set ℝ)ᶜ)).toReal = 0
  rw [hMeasure]
  simp

/-- Support-level restriction localization implies ambient complement
annihilation. -/
theorem explicit_wightman_os_ambient_complement_annihilation_of_scalarMeasure_restriction
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hRestriction :
      ExplicitWightmanOSAmbientEigenvectorScalarMeasureRestrictionLaw M P) :
    ExplicitWightmanOSAmbientEigenvectorComplementAnnihilationLaw M := by
  exact
    explicit_wightman_os_ambient_complement_annihilation_of_scalarMeasure_localization
      M P
        (explicit_wightman_os_ambient_scalarMeasure_localization_of_restriction
          M P hRestriction)

/-- Support-level restriction localization implies the ambient singleton
projection law. -/
theorem explicit_wightman_os_ambient_eigenprojection_law_of_scalarMeasure_restriction
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hRestriction :
      ExplicitWightmanOSAmbientEigenvectorScalarMeasureRestrictionLaw M P) :
    ExplicitWightmanOSAmbientEigenprojectionLaw M := by
  exact
    explicit_wightman_os_ambient_eigenprojection_law_of_scalarMeasure_localization
      M P
        (explicit_wightman_os_ambient_scalarMeasure_localization_of_restriction
          M P hRestriction)

/-- Support-level restriction localization also implies the canonical
vacuum-orthogonal singleton projection law. -/
theorem explicit_wightman_os_canonical_eigenprojection_law_of_scalarMeasure_restriction
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hRestriction :
      ExplicitWightmanOSAmbientEigenvectorScalarMeasureRestrictionLaw M P) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M := by
  exact
    explicit_wightman_os_canonical_eigenprojection_law_of_scalarMeasure_localization
      M P
        (explicit_wightman_os_ambient_scalarMeasure_localization_of_restriction
          M P hRestriction)

end

end MathlibAnalytic
end MGAP4D
