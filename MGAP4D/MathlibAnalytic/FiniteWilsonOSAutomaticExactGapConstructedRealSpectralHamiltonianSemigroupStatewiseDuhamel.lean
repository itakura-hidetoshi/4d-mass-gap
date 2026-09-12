import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupStatewiseDuhamel
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- The constructed finite Wilson real spectral semigroup satisfies the
statewise Duhamel / variation-of-constants formula for continuous forcing. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_duhamel_eq_of_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (x : D.StateSpace)
    (f u : ℝ → D.StateSpace)
    (hf : Continuous f)
    (hu0 : u t₀ = x)
    (hu : ∀ t : ℝ,
      HasDerivAt u
        (-((LinearMap.toContinuousLinearMap (D.hamiltonian n)) (u t)) + f t) t) :
    u = fun t : ℝ =>
      D.realSpectralHamiltonianSemigroup n (t - t₀) x +
        ∫ s in t₀..t,
          D.realSpectralHamiltonianSemigroup n (t - s) (f s) := by
  have hudiag : ∀ t : ℝ,
      HasDerivAt u
        (-(orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) (u t)) + f t) t := by
    intro t
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hu t
  have h := orthonormalDiagonalHamiltonianSemigroup_duhamel_eq_of_hasDerivAt
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    t₀ x f u hf hu0 hudiag
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup]
    using h

end

end MathlibAnalytic
end MGAP4D
