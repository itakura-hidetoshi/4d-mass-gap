import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupEvolution
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupGenerator

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The physical vacuum-orthogonal real spectral semigroup solves the left
evolution equation at every time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    HasDerivAt
      (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n)
      ((-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) *
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t) t :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_left
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t

/-- The physical vacuum-orthogonal real spectral semigroup solves the commuting
right evolution equation at every time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    HasDerivAt
      (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n)
      (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t *
        (-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n))) t :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_right
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t

/-- Statewise all-time evolution equation on the physical excitation sector. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (x : D.gapData.ExcitedStateSpace) :
    HasDerivAt
      (fun s : ℝ =>
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n s x)
      (-(D.gapData.restrictedHamiltonian n
        (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t x))) t :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t x

/-- Ordinary derivative form of the physical all-time evolution equation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_deriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (x : D.gapData.ExcitedStateSpace) :
    deriv
        (fun s : ℝ =>
          D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n s x)
        t =
      -(D.gapData.restrictedHamiltonian n
        (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t x)) :=
  finite_wilson_constructed_real_spectral_hamiltonianSemigroup_deriv
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t x

end

end MathlibAnalytic
end MGAP4D
