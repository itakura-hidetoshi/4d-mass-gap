import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

set_option maxHeartbeats 1000000

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

example :
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.hamiltonian n =
      D.gapData.restrictedHamiltonian n :=
  finite_wilson_vacuum_orthogonal_constructed_hamiltonian_eq_restrictedHamiltonian
    D n

example (t : ℝ) :
    LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) *
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t =
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t *
        LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_commutes_hamiltonian_explicit
    D n t

example (t : ℝ) :
    NormedSpace.exp
        (-(t • LinearMap.toContinuousLinearMap
          (D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.hamiltonian n))) =
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t :=
  finite_wilson_vacuum_orthogonal_normedSpace_exp_neg_restrictedHamiltonian_eq_real_spectralSemigroup
    D n t

example (t : ℝ) :
    (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((NormedSpace.exp
          (-(t • LinearMap.toContinuousLinearMap
            (D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.hamiltonian n)))).toLinearMap.baseChange ℂ) =
      (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t).toLinearMap.comp
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap :=
  finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtension_intertwines_real_operatorExp
    D n t

end

end MathlibAnalytic
end MGAP4D
