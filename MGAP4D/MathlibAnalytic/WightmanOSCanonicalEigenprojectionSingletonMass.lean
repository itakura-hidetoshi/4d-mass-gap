import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPointSpectrum
import MGAP4D.MathlibAnalytic.WightmanOSNonzeroSpectralPVMWitnessFromSingletonMass

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Spectral-theorem compatibility for eigenvectors of the actual canonical
vacuum-orthogonal Hamiltonian: the singleton spectral projection at an
eigenvalue fixes the corresponding ambient vector. -/
def ExplicitWightmanOSCanonicalEigenprojectionLaw
    (M : ExplicitWightmanOSReconstructedModel) : Prop :=
  ∀ {E : ℝ} (x : M.canonicalVacuumOrthogonalHamiltonian.domain),
    M.canonicalVacuumOrthogonalHamiltonian x =
        E • (x : M.VacuumOrthogonalHilbert) →
      M.spectralPVM.projection ({E} : Set ℝ)
          ((x : M.VacuumOrthogonalHilbert) : M.H) =
        ((x : M.VacuumOrthogonalHilbert) : M.H)

/-- A nonzero canonical eigenvector has nonzero singleton PVM projection under
the eigenprojection law. -/
theorem canonical_eigenvector_singleton_projection_ne_zero
    {M : ExplicitWightmanOSReconstructedModel}
    (hEigenprojection : ExplicitWightmanOSCanonicalEigenprojectionLaw M)
    {E : ℝ} (x : M.canonicalVacuumOrthogonalHamiltonian.domain)
    (hx : (x : M.VacuumOrthogonalHilbert) ≠ 0)
    (hEigen : M.canonicalVacuumOrthogonalHamiltonian x =
      E • (x : M.VacuumOrthogonalHilbert)) :
    M.spectralPVM.projection ({E} : Set ℝ)
        ((x : M.VacuumOrthogonalHilbert) : M.H) ≠ 0 := by
  rw [hEigenprojection x hEigen]
  exact fun hZero => hx (Subtype.ext hZero)

/-- A nonzero canonical eigenvector gives positive singleton scalar spectral
mass. -/
theorem canonical_eigenvector_singleton_mass_pos
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (hEigenprojection : ExplicitWightmanOSCanonicalEigenprojectionLaw M)
    {E : ℝ} (x : M.canonicalVacuumOrthogonalHamiltonian.domain)
    (hx : (x : M.VacuumOrthogonalHilbert) ≠ 0)
    (hEigen : M.canonicalVacuumOrthogonalHamiltonian x =
      E • (x : M.VacuumOrthogonalHilbert)) :
    0 < (R.scalarMeasure
      ((x : M.VacuumOrthogonalHilbert) : M.H)).real ({E} : Set ℝ) := by
  exact scalar_spectral_measure_singleton_mass_pos_of_projection_ne_zero
    R _ E
      (canonical_eigenvector_singleton_projection_ne_zero
        hEigenprojection x hx hEigen)

/-- Construct the concrete nonzero PVM witness from a nonzero eigenvector of the
canonical restricted Hamiltonian. -/
def explicitWightmanOSNonzeroSpectralPVMWitnessOfCanonicalEigenvector
    (M : ExplicitWightmanOSReconstructedModel)
    (hEigenprojection : ExplicitWightmanOSCanonicalEigenprojectionLaw M)
    {E : ℝ} (hESpectrum : E ∈ M.hamiltonianEnergySpectrum)
    (hE : E ≠ 0)
    (x : M.canonicalVacuumOrthogonalHamiltonian.domain)
    (hx : (x : M.VacuumOrthogonalHilbert) ≠ 0)
    (hEigen : M.canonicalVacuumOrthogonalHamiltonian x =
      E • (x : M.VacuumOrthogonalHilbert)) :
    ExplicitWightmanOSNonzeroSpectralPVMWitness M :=
  { energy := E
    energy_mem := hESpectrum
    energy_ne_zero := hE
    source := ((x : M.VacuumOrthogonalHilbert) : M.H)
    projected_ne_zero :=
      canonical_eigenvector_singleton_projection_ne_zero
        hEigenprojection x hx hEigen }

/-- The standard PVM composition law and a nonzero canonical eigenvector produce
the physical vacuum-orthogonal spectrum bridge. -/
def explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfCanonicalEigenvector
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    (hEigenprojection : ExplicitWightmanOSCanonicalEigenprojectionLaw M)
    {E : ℝ} (hESpectrum : E ∈ M.hamiltonianEnergySpectrum)
    (hE : E ≠ 0)
    (x : M.canonicalVacuumOrthogonalHamiltonian.domain)
    (hx : (x : M.VacuumOrthogonalHilbert) ≠ 0)
    (hEigen : M.canonicalVacuumOrthogonalHamiltonian x =
      E • (x : M.VacuumOrthogonalHilbert)) :
    ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M :=
  explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVMComposition
    M hComposition
      (explicitWightmanOSNonzeroSpectralPVMWitnessOfCanonicalEigenvector
        M hEigenprojection hESpectrum hE x hx hEigen)

/-- A nonzero canonical eigenvector closes the PVM-based physical gap route. -/
theorem explicit_wightman_os_canonical_eigenvector_vacuum_orthogonal_spectrum_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    (hEigenprojection : ExplicitWightmanOSCanonicalEigenprojectionLaw M)
    {E m : ℝ} (hESpectrum : E ∈ M.hamiltonianEnergySpectrum)
    (hE : E ≠ 0)
    (x : M.canonicalVacuumOrthogonalHamiltonian.domain)
    (hx : (x : M.VacuumOrthogonalHilbert) ≠ 0)
    (hEigen : M.canonicalVacuumOrthogonalHamiltonian x =
      E • (x : M.VacuumOrthogonalHilbert))
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    0 < m ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆ Set.Ici m ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) = m := by
  exact explicit_wightman_os_pvm_composition_vacuum_orthogonal_spectrum_gap
    M hComposition
      (explicitWightmanOSNonzeroSpectralPVMWitnessOfCanonicalEigenvector
        M hEigenprojection hESpectrum hE x hx hEigen)
      hRelGap hmSpectrum

end

end MathlibAnalytic
end MGAP4D
