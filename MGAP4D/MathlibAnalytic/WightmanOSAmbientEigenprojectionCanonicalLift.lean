import MGAP4D.MathlibAnalytic.WightmanOSCanonicalEigenprojectionSingletonMass

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Spectral-theorem compatibility at eigenvectors for a partially-defined
real-linear operator and a projection-valued set function: every eigenvector is
fixed by the singleton projection at its eigenvalue. -/
def OrthogonalProjectionValuedSetFunction.HasEigenprojectionLaw
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (T : H →ₗ.[ℝ] H) : Prop :=
  ∀ {E : ℝ} (x : T.domain), T x = E • (x : H) →
    P.projection ({E} : Set ℝ) (x : H) = (x : H)

/-- The explicit ambient Hamiltonian compatibility law with its declared
spectral PVM. This is the minimal remaining spectral-theorem input before
specializing to the canonical vacuum-orthogonal restriction. -/
def ExplicitWightmanOSAmbientEigenprojectionLaw
    (M : ExplicitWightmanOSReconstructedModel) : Prop :=
  M.spectralPVM.HasEigenprojectionLaw M.hamiltonian

/-- A canonical restricted eigenvector lifts to an ambient Hamiltonian
eigenvector with the same eigenvalue. -/
theorem canonical_eigenvector_ambient_hamiltonian
    (M : ExplicitWightmanOSReconstructedModel)
    {E : ℝ} (x : M.canonicalVacuumOrthogonalHamiltonian.domain)
    (hEigen : M.canonicalVacuumOrthogonalHamiltonian x =
      E • (x : M.VacuumOrthogonalHilbert)) :
    M.hamiltonian (M.vacuumOrthogonalAmbientDomainPoint x) =
      E • ((x : M.VacuumOrthogonalHilbert) : M.H) := by
  calc
    M.hamiltonian (M.vacuumOrthogonalAmbientDomainPoint x) =
        ((M.canonicalVacuumOrthogonalHamiltonian x :
          M.VacuumOrthogonalHilbert) : M.H) :=
      (canonical_vacuum_orthogonal_hamiltonian_apply M x).symm
    _ = ((E • (x : M.VacuumOrthogonalHilbert) :
          M.VacuumOrthogonalHilbert) : M.H) := by
      rw [hEigen]
    _ = E • ((x : M.VacuumOrthogonalHilbert) : M.H) := rfl

/-- Ambient spectral-theorem compatibility implies the canonical restricted
eigenprojection law. Thus the actual restriction contributes no additional
spectral assumption beyond the ambient Hamiltonian/PVM compatibility. -/
theorem explicit_wightman_os_canonical_eigenprojection_law_of_ambient
    (M : ExplicitWightmanOSReconstructedModel)
    (hAmbient : ExplicitWightmanOSAmbientEigenprojectionLaw M) :
    ExplicitWightmanOSCanonicalEigenprojectionLaw M := by
  intro E x hEigen
  simpa [ExplicitWightmanOSAmbientEigenprojectionLaw,
    OrthogonalProjectionValuedSetFunction.HasEigenprojectionLaw] using
    hAmbient (M.vacuumOrthogonalAmbientDomainPoint x)
      (canonical_eigenvector_ambient_hamiltonian M x hEigen)

end

end MathlibAnalytic
end MGAP4D
