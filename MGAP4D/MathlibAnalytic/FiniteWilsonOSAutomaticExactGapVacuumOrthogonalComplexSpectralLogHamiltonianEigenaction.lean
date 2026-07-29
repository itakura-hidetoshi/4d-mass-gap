import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralLogHamiltonianEigenaction
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralLogHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit complex spectral Hamiltonian on the physical excitation sector
`Ω⊥`, obtained through the established coercive-to-constructed route. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexSpectralHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
      D.vacuumOrthogonalComplexSpectralStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.complexSpectralHamiltonian n

/-- The explicit complex spectral excitation Hamiltonian is positive. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonian_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    (D.vacuumOrthogonalComplexSpectralHamiltonian n).IsPositive :=
  finite_wilson_constructed_complex_spectral_hamiltonian_isPositive
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Exponentiating the negative explicit excitation Hamiltonian recovers the
vacuum-orthogonal complex spectral transfer operator. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_exp_neg_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    NormedSpace.exp (-D.vacuumOrthogonalComplexSpectralHamiltonian n) =
      D.vacuumOrthogonalComplexSpectralTransferOperator n :=
  finite_wilson_constructed_complex_spectral_exp_neg_hamiltonian
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- On the physical excitation sector, the canonical CFC logarithmic
Hamiltonian is exactly the explicit Hamiltonian diagonal operator. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_eq_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralLogHamiltonian n =
      D.vacuumOrthogonalComplexSpectralHamiltonian n :=
  finite_wilson_constructed_complex_spectral_logHamiltonian_eq_hamiltonian
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The recovered excitation-sector logarithmic Hamiltonian acts on mode `i`
by the corresponding restricted Hamiltonian energy eigenvalue. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalComplexSpectralLogHamiltonian n
        (D.vacuumOrthogonalComplexSpectralBasis i) =
      ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
          D.gapData n).eigenvalues D.gapData.excitedFinrank i : ℂ) •
        D.vacuumOrthogonalComplexSpectralBasis i :=
  finite_wilson_constructed_complex_spectral_logHamiltonian_on_basis
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n i

end

end MathlibAnalytic
end MGAP4D
