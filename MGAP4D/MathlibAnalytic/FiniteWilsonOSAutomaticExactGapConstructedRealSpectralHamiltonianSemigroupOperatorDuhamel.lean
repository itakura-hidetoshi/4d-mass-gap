import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamel
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- Constructed finite Wilson operator-valued Duhamel formula for the left
Hamiltonian equation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U t + F t) t) :
    U = fun t : ℝ =>
      D.realSpectralHamiltonianSemigroup n (t - t₀) * A +
        ∫ s in t₀..t, D.realSpectralHamiltonianSemigroup n (t - s) * F s := by
  have hUdiag : ∀ t : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U t + F t) t := by
    intro t
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU t
  have h := orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    t₀ A F U hF hU0 hUdiag
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup]
    using h

/-- Constructed finite Wilson operator-valued Duhamel formula for the right
Hamiltonian equation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F t) t) :
    U = fun t : ℝ =>
      A * D.realSpectralHamiltonianSemigroup n (t - t₀) +
        ∫ s in t₀..t, F s * D.realSpectralHamiltonianSemigroup n (t - s) := by
  have hUdiag : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F t) t := by
    intro t
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU t
  have h := orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    t₀ A F U hF hU0 hUdiag
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup]
    using h

end

end MathlibAnalytic
end MGAP4D
