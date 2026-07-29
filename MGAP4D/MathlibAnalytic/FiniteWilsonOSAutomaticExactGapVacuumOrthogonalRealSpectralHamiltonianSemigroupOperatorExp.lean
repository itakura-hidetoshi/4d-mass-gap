import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorExp
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupEvolution

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

set_option maxHeartbeats 1000000

local instance finiteWilsonVacuumOrthogonalExcitedStateCompleteSpace
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W) :
    CompleteSpace D.gapData.ExcitedStateSpace :=
  FiniteDimensional.complete ℝ D.gapData.ExcitedStateSpace

/-- Ordinary operator-norm derivative form of the physical left evolution
equation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_deriv_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    deriv (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n) t =
      (-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) *
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t :=
  (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_left
    D n t).deriv

/-- Ordinary operator-norm derivative form of the physical right evolution
equation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_deriv_operator_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    deriv (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n) t =
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t *
        (-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) :=
  (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_right
    D n t).deriv

/-- The restricted physical real Hamiltonian commutes with every
vacuum-orthogonal spectral time slice. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_commutes_hamiltonian_explicit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) *
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t =
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t *
        LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_commutes_hamiltonian_explicit
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t

/-- The physical vacuum-orthogonal real spectral semigroup is exactly the
operator exponential of the negative time-scaled restricted Hamiltonian. -/
theorem finite_wilson_vacuum_orthogonal_normedSpace_exp_neg_restrictedHamiltonian_eq_real_spectralSemigroup
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    NormedSpace.exp
        (-(t • LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n))) =
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t :=
  finite_wilson_constructed_normedSpace_exp_neg_hamiltonian_eq_real_spectralSemigroup
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t

/-- Literal complex scalar extension intertwines the physical real restricted
Hamiltonian exponential with the complex spectral excitation semigroup. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_scalarExtension_intertwines_real_operatorExp
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((NormedSpace.exp
          (-(t • LinearMap.toContinuousLinearMap
            (D.gapData.restrictedHamiltonian n)))).toLinearMap.baseChange ℂ) =
      (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t).toLinearMap.comp
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n).toLinearMap :=
  finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_real_operatorExp
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t

end

end MathlibAnalytic
end MGAP4D
