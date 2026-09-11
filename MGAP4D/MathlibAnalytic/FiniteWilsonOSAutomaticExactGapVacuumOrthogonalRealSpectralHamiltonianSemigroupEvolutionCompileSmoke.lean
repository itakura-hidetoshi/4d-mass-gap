import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupEvolution

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

example (t : ℝ) :
    HasDerivAt
      (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n)
      ((-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) *
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t) t :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_left
    D n t

example (t : ℝ) :
    HasDerivAt
      (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n)
      (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t *
        (-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n))) t :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_right
    D n t

example (t : ℝ) (x : D.gapData.ExcitedStateSpace) :
    HasDerivAt
      (fun s : ℝ =>
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n s x)
      (-(D.gapData.restrictedHamiltonian n
        (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t x))) t :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt
    D n t x

example (t : ℝ) (x : D.gapData.ExcitedStateSpace) :
    deriv
        (fun s : ℝ =>
          D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n s x)
        t =
      -(D.gapData.restrictedHamiltonian n
        (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t x)) :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_deriv
    D n t x

end

end MathlibAnalytic
end MGAP4D
