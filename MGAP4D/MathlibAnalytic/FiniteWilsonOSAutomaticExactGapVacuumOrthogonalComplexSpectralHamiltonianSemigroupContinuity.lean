import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralHamiltonianSemigroupContinuity
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralHamiltonianSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The vacuum-orthogonal complex spectral Hamiltonian semigroup is smooth in
operator norm. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_contDiff
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiff ℝ ⊤ (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n) :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_contDiff
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The vacuum-orthogonal complex spectral Hamiltonian semigroup is continuous
in operator norm. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_continuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    Continuous (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n) :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_continuous
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The vacuum-orthogonal excitation-sector semigroup is strongly continuous on
every state vector, without a new assumption on the vacuum line. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_stronglyContinuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.vacuumOrthogonalComplexSpectralStateSpace) :
    Continuous (fun t : ℝ =>
      D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x) :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_stronglyContinuous
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

end

end MathlibAnalytic
end MGAP4D
