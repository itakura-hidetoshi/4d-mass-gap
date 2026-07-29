import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralScalarExtension
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralHamiltonianSemigroupGenerator

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

/-- The literal complex scalar extension of the physical real excitation sector
`Ω⊥`. -/
abbrev
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexScalarExtensionStateSpace
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W) :
    Type :=
  ℂ ⊗[ℝ] D.gapData.ExcitedStateSpace

/-- The existing complex spectral excitation space is literally equivalent to
`ℂ ⊗[ℝ] Ω⊥`, through the established coercive-to-constructed route. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexSpectralScalarExtensionEquiv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexScalarExtensionStateSpace ≃ₗ[ℂ]
      D.vacuumOrthogonalComplexSpectralStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.complexSpectralScalarExtensionEquiv n

/-- The physical scalar-extension equivalence identifies `1 ⊗ eᵢ` with the
corresponding complex excitation mode. -/
@[simp]
theorem finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtensionEquiv_one_tmul_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n
        (1 ⊗ₜ[ℝ]
          ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
            D.gapData n).eigenvectorBasis D.gapData.excitedFinrank i)) =
      D.vacuumOrthogonalComplexSpectralBasis i :=
  finite_wilson_constructed_complex_spectral_scalarExtensionEquiv_one_tmul_basis
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n i

/-- The real continuous-time spectral semigroup on the physical excitation
sector before complex scalar extension. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalRealSpectralHamiltonianSemigroup
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.realSpectralHamiltonianSemigroup n t

/-- Time zero is the identity on the physical real excitation sector. -/
@[simp]
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n 0 = 1 :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_zero
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The physical real spectral time slices satisfy the semigroup law. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_add
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (s t : ℝ) :
    D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (s + t) =
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n s *
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_add
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n s t

/-- Time one recovers the original physical real transfer operator. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n 1 =
      D.vacuumOrthogonalTransferOperator n :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_one
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Literal scalar extension intertwines the physical real transfer operator
with the complex spectral transfer operator. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtension_intertwines_transfer
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.vacuumOrthogonalTransferOperator n).toLinearMap.baseChange ℂ) =
      (D.vacuumOrthogonalComplexSpectralTransferOperator n).toLinearMap.comp
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap :=
  finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_transfer
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Literal scalar extension identifies the restricted physical real
Hamiltonian with the explicit complex spectral Hamiltonian. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtension_intertwines_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.gapData.restrictedHamiltonian n).baseChange ℂ) =
      (D.vacuumOrthogonalComplexSpectralHamiltonian n).toLinearMap.comp
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap :=
  finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_hamiltonian
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Literal scalar extension identifies the restricted physical real
Hamiltonian with the canonical complex logarithmic Hamiltonian. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtension_intertwines_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.gapData.restrictedHamiltonian n).baseChange ℂ) =
      (D.vacuumOrthogonalComplexSpectralLogHamiltonian n).toLinearMap.comp
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap :=
  finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_logHamiltonian
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Literal scalar extension intertwines every physical real spectral time
slice with the complex continuous-time Hamiltonian semigroup. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtension_intertwines_semigroup
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t).toLinearMap.baseChange ℂ) =
      (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t).toLinearMap.comp
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap :=
  finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_semigroup
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t

end

end MathlibAnalytic
end MGAP4D
