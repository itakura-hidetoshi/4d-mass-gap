import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorFamilyUniformProductSetBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorUniformUnitBallMatrixElementBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The same closed-ball unit-state Taylor error envelope controls every
constructed finite Wilson approximation index. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls_allIndices
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (N : ℕ) {lambda r mu : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (n : ℕ) (x y : D.StateSpace)
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
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls_family
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hmu N n x y hx hy)

/-- One eventual Taylor degree controls every constructed finite Wilson index,
every parameter in the closed subgap ball, and both state unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_eventually_error_abs_lt_closedBall_unitBalls_allIndices
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      ∀ n : ℕ, ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x
            ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
              ∑ k ∈ Finset.range N,
                ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
                  (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
                  lambda) y)| < epsilon := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_eventually_error_abs_lt_closedBall_unitBalls_family
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hepsilon)

/-- A single epsilon-dependent threshold works simultaneously for all later
Taylor degrees and all constructed finite Wilson approximation indices. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_exists_uniform_truncationOrder_closedBall_unitBalls_allIndices
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ n : ℕ, ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x
            ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
              ∑ k ∈ Finset.range N,
                ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
                  (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
                  lambda) y)| < epsilon := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_exists_uniform_truncationOrder_closedBall_unitBalls_family
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hepsilon)

/-- Constructed finite Wilson Taylor matrix elements converge uniformly on the
product of all approximation indices, the closed spectral-parameter ball, and
the two closed state unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_partialSum_tendstoUniformlyOn_allIndices_closedBall_unitBalls
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : ℕ × (ℝ × (D.StateSpace × D.StateSpace)) =>
        inner ℝ p.2.2.1
          ((∑ k ∈ Finset.range N,
            ((p.2.1 - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
              (finite_wilson_constructed_real_spectral_hamiltonianResolvent D p.1)
              lambda) p.2.2.2))
      (fun p : ℕ × (ℝ × (D.StateSpace × D.StateSpace)) =>
        inner ℝ p.2.2.1
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D p.1
            p.2.1 p.2.2.2))
      atTop
      ((Set.univ : Set ℕ) ×ˢ
        (Metric.closedBall lambda r ×ˢ
          (Metric.closedBall (0 : D.StateSpace) 1 ×ˢ
            Metric.closedBall (0 : D.StateSpace) 1))) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_partialSum_tendstoUniformlyOn_family_closedBall_unitBalls
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt)

end MathlibAnalytic
end MGAP4D

end