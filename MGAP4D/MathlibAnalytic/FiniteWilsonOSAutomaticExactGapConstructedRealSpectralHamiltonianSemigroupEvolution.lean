import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupEvolution
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupGenerator

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The constructed real spectral semigroup solves `S'_t = -H S_t` in operator
norm at every time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    HasDerivAt
      (D.realSpectralHamiltonianSemigroup n)
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) *
        D.realSpectralHamiltonianSemigroup n t) t := by
  have hdiag := symmetric_eq_orthonormalDiagonalLinearMap
    (D.hamiltonian n) (D.hamiltonianSymmetric n) D.stateFinrank
  have hop :
      orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) =
        LinearMap.toContinuousLinearMap (D.hamiltonian n) := by
    unfold orthonormalDiagonalOperator
    exact congrArg LinearMap.toContinuousLinearMap hdiag.symm
  have h := orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) t
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup,
    orthonormalDiagonalHamiltonianSemigroup, hop] using h

/-- The constructed real spectral semigroup also solves the commuting right
evolution equation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    HasDerivAt
      (D.realSpectralHamiltonianSemigroup n)
      (D.realSpectralHamiltonianSemigroup n t *
        (-LinearMap.toContinuousLinearMap (D.hamiltonian n))) t := by
  have hdiag := symmetric_eq_orthonormalDiagonalLinearMap
    (D.hamiltonian n) (D.hamiltonianSymmetric n) D.stateFinrank
  have hop :
      orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) =
        LinearMap.toContinuousLinearMap (D.hamiltonian n) := by
    unfold orthonormalDiagonalOperator
    exact congrArg LinearMap.toContinuousLinearMap hdiag.symm
  have h := orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) t
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup,
    orthonormalDiagonalHamiltonianSemigroup, hop] using h

/-- Statewise all-time evolution equation on the constructed real state space. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (x : D.StateSpace) :
    HasDerivAt
      (fun s : ℝ => D.realSpectralHamiltonianSemigroup n s x)
      (-(D.hamiltonian n
        (D.realSpectralHamiltonianSemigroup n t x))) t := by
  have h :=
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_left
      D n t).clm_apply (hasDerivAt_const t x)
  simpa using h

/-- Ordinary derivative form of the constructed all-time evolution equation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_deriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (x : D.StateSpace) :
    deriv (fun s : ℝ => D.realSpectralHamiltonianSemigroup n s x) t =
      -(D.hamiltonian n
        (D.realSpectralHamiltonianSemigroup n t x)) :=
  (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt
    D n t x).deriv

end

end MathlibAnalytic
end MGAP4D
