import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupStatewiseArbitraryInitialTimeIVPUniqueness
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every statewise solution of the constructed finite Wilson Hamiltonian IVP,
based at an arbitrary initial time `t₀`, is the corresponding translated real
spectral semigroup orbit. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_apply_sub_eq_of_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (x : D.StateSpace)
    (u : ℝ → D.StateSpace)
    (hu0 : u t₀ = x)
    (hu : ∀ t : ℝ,
      HasDerivAt u
        (-((LinearMap.toContinuousLinearMap (D.hamiltonian n)) (u t))) t) :
    u = fun t : ℝ => D.realSpectralHamiltonianSemigroup n (t - t₀) x := by
  have hudiag : ∀ t : ℝ,
      HasDerivAt u
        (-(orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) (u t))) t := by
    intro t
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hu t
  have h := orthonormalDiagonalHamiltonianSemigroup_apply_sub_eq_of_hasDerivAt
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    t₀ x u hu0 hudiag
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup]
    using h

end

end MathlibAnalytic
end MGAP4D
