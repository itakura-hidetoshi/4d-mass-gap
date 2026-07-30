import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorUniformUnitBallMatrixElementBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorStateMatrixElementBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- On the two closed unit balls, the constructed finite Wilson matrix-element
Taylor truncation is bounded by the bare exact-gap geometric envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda r mu : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (x y : D.StateSpace)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y)| ≤
      (r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hmu N x y hx hy)

/-- One eventual Taylor degree controls all constructed finite Wilson real
matrix elements simultaneously on the parameter ball and both state unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_eventually_error_abs_lt_closedBall_unitBalls
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda r epsilon : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x
            ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
              ∑ k ∈ Finset.range N,
                ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
                  (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
                  lambda) y)| < epsilon := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_eventually_error_abs_lt_closedBall_unitBalls
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hepsilon)

/-- Epsilon-dependent simultaneous Taylor threshold for the constructed finite
Wilson Hamiltonian resolvent on the parameter ball and both state unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_exists_uniform_truncationOrder_closedBall_unitBalls
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda r epsilon : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x
            ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
              ∑ k ∈ Finset.range N,
                ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
                  (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
                  lambda) y)| < epsilon := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_exists_uniform_truncationOrder_closedBall_unitBalls
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hepsilon)

end MathlibAnalytic
end MGAP4D

end
