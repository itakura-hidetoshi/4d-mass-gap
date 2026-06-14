import MGAP4D.MathlibAnalytic.WightmanOSVacuumOrthogonalHamiltonianInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Operator-level physical gap theorem.  The same bridge now exposes the actual
canonical restriction `H|Ω⊥`, its basic analytic properties, and the strictly
positive lower edge of the associated non-vacuum spectral set. -/
theorem canonical_vacuum_orthogonal_hamiltonian_spectrum_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian ∧
      Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
        Set M.VacuumOrthogonalHilbert)) ∧
      LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian ∧
      0 < m ∧
      B.restrictedSpectrum ⊆ Set.Ici m ∧
      sInf B.restrictedSpectrum = m := by
  have hSpectral :=
    explicit_wightman_os_vacuum_orthogonal_spectrum_gap
      M B.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
        hRelGap hmSpectrum
  exact ⟨B.canonicalRestrictedSelfAdjoint,
    canonical_vacuum_orthogonal_hamiltonian_dense_domain B,
    canonical_vacuum_orthogonal_hamiltonian_isClosed B,
    hSpectral.1, hSpectral.2.1, hSpectral.2.2⟩

/-- Exact-value specialization of the actual restricted-Hamiltonian theorem. -/
theorem canonical_vacuum_orthogonal_hamiltonian_exact_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian ∧
      Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
        Set M.VacuumOrthogonalHilbert)) ∧
      LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian ∧
      0 < exactGapValueReal ∧
      B.restrictedSpectrum ⊆ Set.Ici exactGapValueReal ∧
      sInf B.restrictedSpectrum = exactGapValueReal := by
  exact canonical_vacuum_orthogonal_hamiltonian_spectrum_gap
    M B hRelGap hExactSpectrum

/-- Full certificate combining the actual restricted operator with the physical
non-vacuum spectral edge. -/
structure ExplicitWightmanOSCanonicalRestrictedHamiltonianGapCertificate
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M)
    (m : ℝ) where
  operatorSelfAdjoint :
    IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian
  operatorDomain :
    M.canonicalVacuumOrthogonalHamiltonian.domain =
      M.vacuumOrthogonalHamiltonianDomain
  operatorDomainDense :
    Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
      Set M.VacuumOrthogonalHilbert))
  operatorClosed :
    LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian
  spectrumEqNonvacuum :
    B.restrictedSpectrum =
      M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)
  gapPositive : 0 < m
  spectrumLowerBound : B.restrictedSpectrum ⊆ Set.Ici m
  spectrumInfimum : sInf B.restrictedSpectrum = m

/-- Construct the operator-and-spectrum certificate from the canonical bridge. -/
def explicitWightmanOSCanonicalRestrictedHamiltonianGapCertificate
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSCanonicalRestrictedHamiltonianGapCertificate M B m := by
  have hGap := canonical_vacuum_orthogonal_hamiltonian_spectrum_gap
    M B hRelGap hmSpectrum
  exact
    { operatorSelfAdjoint := hGap.1
      operatorDomain := canonical_vacuum_orthogonal_hamiltonian_domain M
      operatorDomainDense := hGap.2.1
      operatorClosed := hGap.2.2.1
      spectrumEqNonvacuum := B.restrictedSpectrum_eq_nonvacuum
      gapPositive := hGap.2.2.2.1
      spectrumLowerBound := hGap.2.2.2.2.1
      spectrumInfimum := hGap.2.2.2.2.2 }

end

end MathlibAnalytic
end MGAP4D
