import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelUniformForcingGain
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelMassGapBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left Duhamel evolution has the exact finite-time
uniform-forcing gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) /
          exactGapValueReal) * M := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_left
      (M := M)
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A F U hF hFM hU0 hUdiag

/-- Constructed finite Wilson right Duhamel evolution has the same exact
finite-time uniform-forcing gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) /
          exactGapValueReal) * M := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_right
      (M := M)
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A F U hF hFM hU0 hUdiag

/-- Constructed finite Wilson left evolution is bounded by its decaying transient
plus the static exact-gap input gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        M / exactGapValueReal := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A F U M hM hF hFM hU0 hUdiag

/-- Constructed finite Wilson right evolution has the same static exact-gap input
gain, without a commutation hypothesis. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        M / exactGapValueReal := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A F U M hM hF hFM hU0 hUdiag

end

end MathlibAnalytic
end MGAP4D
