import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupGenerator
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralScalarExtension

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The physical vacuum-orthogonal real spectral semigroup is smooth in
operator norm. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_contDiff
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiff ℝ ⊤ (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n) :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_contDiff
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The physical vacuum-orthogonal real spectral semigroup is continuous in
operator norm. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_continuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    Continuous (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n) :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_continuous
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The physical vacuum-orthogonal real spectral semigroup is strongly
continuous on every excitation state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_stronglyContinuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.gapData.ExcitedStateSpace) :
    Continuous (fun t : ℝ =>
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t x) :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_stronglyContinuous
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

/-- In operator norm, the physical real excitation semigroup has generator
minus the restricted Hamiltonian. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_zero_operator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    HasDerivAt
      (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n)
      (-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) 0 :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_zero_operator
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- On every physical real excitation state, the strong derivative at time zero
is minus the restricted Hamiltonian action. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.gapData.ExcitedStateSpace) :
    HasDerivAt
      (fun t : ℝ =>
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t x)
      (-(D.gapData.restrictedHamiltonian n x)) 0 :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_zero
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

/-- Ordinary derivative form of the physical real excitation generator. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_deriv_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.gapData.ExcitedStateSpace) :
    deriv
        (fun t : ℝ =>
          D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t x)
        0 =
      -(D.gapData.restrictedHamiltonian n x) :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_deriv_zero
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

/-- Literal scalar extension transports the physical real generator to the
explicit complex spectral generator. -/
theorem finite_wilson_vacuum_orthogonal_complex_scalarExtension_generator_compatible
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (y : D.vacuumOrthogonalComplexScalarExtensionStateSpace) :
    HasDerivAt
      (fun t : ℝ =>
        D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t
          (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n y))
      (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n
        (-((D.gapData.restrictedHamiltonian n).baseChange ℂ y))) 0 :=
  finite_wilson_constructed_complex_scalarExtension_generator_compatible
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n y

/-- The transported physical generator is also the negative canonical complex
logarithmic Hamiltonian. -/
theorem finite_wilson_vacuum_orthogonal_complex_scalarExtension_logGenerator_compatible
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (y : D.vacuumOrthogonalComplexScalarExtensionStateSpace) :
    HasDerivAt
      (fun t : ℝ =>
        D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t
          (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n y))
      (-(D.vacuumOrthogonalComplexSpectralLogHamiltonian n
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n y))) 0 :=
  finite_wilson_constructed_complex_scalarExtension_logGenerator_compatible
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n y

end

end MathlibAnalytic
end MGAP4D
