import MGAP4D.MathlibAnalytic.WightmanOSEigenvectorScalarMeasureRestriction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Off-eigenvalue scalar spectral vanishing for ambient Hamiltonian eigenvectors:
every measurable energy set disjoint from the eigenvalue singleton has zero scalar
spectral mass.  This is the natural scalar consequence expected from a spectral
integral or functional-calculus intertwining law. -/
def ExplicitWightmanOSAmbientEigenvectorOffEnergyScalarVanishingLaw
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M) : Prop :=
  ∀ {E : ℝ} (x : M.hamiltonian.domain),
    M.hamiltonian x = E • (x : M.H) →
      ∀ (s : Set ℝ), MeasurableSet s → Disjoint s ({E} : Set ℝ) →
        P.scalarMeasure (x : M.H) s = 0

/-- Vanishing on every measurable set disjoint from the eigenvalue implies that
the scalar spectral measure restricted to the eigenvalue complement is zero. -/
theorem explicit_wightman_os_ambient_scalarMeasure_restriction_of_offEnergy_vanishing
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hVanishing :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyScalarVanishingLaw M P) :
    ExplicitWightmanOSAmbientEigenvectorScalarMeasureRestrictionLaw M P := by
  intro E x hEigen
  ext s hs
  rw [Measure.restrict_apply (MeasurableSet.singleton E).compl]
  have hMeasurable : MeasurableSet (s ∩ ({E} : Set ℝ)ᶜ) :=
    hs.inter (MeasurableSet.singleton E).compl
  have hDisjoint : Disjoint (s ∩ ({E} : Set ℝ)ᶜ) ({E} : Set ℝ) := by
    simp
  rw [hVanishing x hEigen (s ∩ ({E} : Set ℝ)ᶜ) hMeasurable hDisjoint]
  simp

/-- Off-eigenvalue scalar vanishing implies the complement real-mass
localization law. -/
theorem explicit_wightman_os_ambient_scalarMeasure_localization_of_offEnergy_vanishing
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hVanishing :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyScalarVanishingLaw M P) :
    ExplicitWightmanOSAmbientEigenvectorScalarMeasureLocalizationLaw M P := by
  exact explicit_wightman_os_ambient_scalarMeasure_localization_of_restriction
    M P
      (explicit_wightman_os_ambient_scalarMeasure_restriction_of_offEnergy_vanishing
        M P hVanishing)

/-- Off-eigenvalue scalar vanishing implies ambient complement annihilation. -/
theorem explicit_wightman_os_ambient_complement_annihilation_of_offEnergy_vanishing
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hVanishing :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyScalarVanishingLaw M P) :
    ExplicitWightmanOSAmbientEigenvectorComplementAnnihilationLaw M := by
  exact explicit_wightman_os_ambient_complement_annihilation_of_scalarMeasure_restriction
    M P
      (explicit_wightman_os_ambient_scalarMeasure_restriction_of_offEnergy_vanishing
        M P hVanishing)

/-- Off-eigenvalue scalar vanishing implies the ambient singleton projection law. -/
theorem explicit_wightman_os_ambient_eigenprojection_law_of_offEnergy_vanishing
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hVanishing :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyScalarVanishingLaw M P) :
    ExplicitWightmanOSAmbientEigenprojectionLaw M := by
  exact explicit_wightman_os_ambient_eigenprojection_law_of_scalarMeasure_restriction
    M P
      (explicit_wightman_os_ambient_scalarMeasure_restriction_of_offEnergy_vanishing
        M P hVanishing)

/-- Off-eigenvalue scalar vanishing also implies the canonical vacuum-orthogonal
singleton projection law. -/
theorem explicit_wightman_os_canonical_eigenprojection_law_of_offEnergy_vanishing
    (M : ExplicitWightmanOSReconstructedModel)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure M)
    (hVanishing :
      ExplicitWightmanOSAmbientEigenvectorOffEnergyScalarVanishingLaw M P) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M := by
  exact explicit_wightman_os_canonical_eigenprojection_law_of_scalarMeasure_restriction
    M P
      (explicit_wightman_os_ambient_scalarMeasure_restriction_of_offEnergy_vanishing
        M P hVanishing)

end

end MathlibAnalytic
end MGAP4D
