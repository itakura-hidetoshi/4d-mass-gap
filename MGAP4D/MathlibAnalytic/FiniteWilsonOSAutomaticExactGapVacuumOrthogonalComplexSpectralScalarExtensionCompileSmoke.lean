import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralScalarExtension

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

example :
    D.vacuumOrthogonalComplexScalarExtensionStateSpace ≃ₗ[ℂ]
      D.vacuumOrthogonalComplexSpectralStateSpace :=
  D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n

example (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n
        (1 ⊗ₜ[ℝ]
          ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
            D.gapData n).eigenvectorBasis D.gapData.excitedFinrank i)) =
      D.vacuumOrthogonalComplexSpectralBasis i :=
  finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtensionEquiv_one_tmul_basis
    D n i

example :
    D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n 0 = 1 :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_zero D n

example (s t : ℝ) :
    D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (s + t) =
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n s *
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_add D n s t

example :
    D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n 1 =
      D.vacuumOrthogonalTransferOperator n :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_one D n

example :
    (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.vacuumOrthogonalTransferOperator n).toLinearMap.baseChange ℂ) =
      (D.vacuumOrthogonalComplexSpectralTransferOperator n).toLinearMap.comp
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap :=
  finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtension_intertwines_transfer
    D n

example :
    (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.gapData.restrictedHamiltonian n).baseChange ℂ) =
      (D.vacuumOrthogonalComplexSpectralLogHamiltonian n).toLinearMap.comp
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap :=
  finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtension_intertwines_logHamiltonian
    D n

example (t : ℝ) :
    (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t).toLinearMap.baseChange ℂ) =
      (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t).toLinearMap.comp
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap :=
  finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtension_intertwines_semigroup
    D n t

end

end MathlibAnalytic
end MGAP4D
