import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelMassGapBound
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamel

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- Constructed finite Wilson left operator-valued Duhamel response is damped by
the exact Hamiltonian gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_massGap_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        ∫ s in t₀..t,
          Real.exp (-((t - s) * exactGapValueReal)) * ‖F s‖ := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A F U hF hU0 hUdiag

/-- Constructed finite Wilson right operator-valued Duhamel response is damped by
the exact Hamiltonian gap, without a commutation hypothesis on the data. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_massGap_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        ∫ s in t₀..t,
          Real.exp (-((t - s) * exactGapValueReal)) * ‖F s‖ := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A F U hF hU0 hUdiag

end

end MathlibAnalytic
end MGAP4D
