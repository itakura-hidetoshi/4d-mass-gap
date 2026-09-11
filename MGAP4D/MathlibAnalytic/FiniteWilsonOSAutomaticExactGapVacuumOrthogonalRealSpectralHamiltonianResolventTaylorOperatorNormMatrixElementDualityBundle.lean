import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorOperatorNormMatrixElementDualityBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventTaylorFamilyUniformProductSetBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- For a finite Wilson `Ω⊥` Taylor remainder, an operator-norm bound is exactly
equivalent to the corresponding two-unit-ball matrix-element bound. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_taylor_partialSum_norm_le_iff_matrixElement_le_unitBalls
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu C : ℝ} (hC : 0 ≤ C) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
            lambda)‖ ≤ C ↔
      ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x
          ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
            ∑ k ∈ Finset.range N,
              ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
                (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
                lambda) y)| ≤ C := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_taylor_partialSum_norm_le_iff_matrixElement_le_unitBalls
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n N hC

/-- The same operator-norm Taylor error envelope controls every finite Wilson
`Ω⊥` approximation index. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall_allIndices
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (N : ℕ) {lambda r mu : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (n : ℕ) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
            lambda)‖ ≤
      (r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall_allIndices
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      N hlambda hr0 hrlt hmu n

/-- One eventual Taylor degree controls the operator-norm remainder for every
finite Wilson `Ω⊥` approximation index. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_eventually_operatorNorm_error_lt_closedBall_allIndices
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      ∀ n : ℕ, ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
          (∑ k ∈ Finset.range N,
            ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
              (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
              lambda)‖ < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_eventually_operatorNorm_error_lt_closedBall_allIndices
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      hlambda hr0 hrlt hepsilon

/-- A single epsilon-dependent threshold controls the operator-norm Taylor
remainder for every later degree and every finite Wilson `Ω⊥` index. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_exists_uniform_operatorNorm_truncationOrder_closedBall_allIndices
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ n : ℕ, ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
          (∑ k ∈ Finset.range N,
            ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
              (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
              lambda)‖ < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_exists_uniform_operatorNorm_truncationOrder_closedBall_allIndices
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      hlambda hr0 hrlt hepsilon

/-- Finite Wilson `Ω⊥` Taylor partial sums converge uniformly in operator norm
on the product of all approximation indices and the closed parameter ball. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_partialSum_tendstoUniformlyOn_operatorNorm_allIndices_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    {lambda r : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : ℕ × ℝ =>
        ∑ k ∈ Finset.range N,
          ((p.2 - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D p.1)
            lambda)
      (fun p : ℕ × ℝ =>
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D p.1 p.2)
      atTop
      ((Set.univ : Set ℕ) ×ˢ Metric.closedBall lambda r) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_partialSum_tendstoUniformlyOn_operatorNorm_allIndices_closedBall
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      hlambda hr0 hrlt

end MathlibAnalytic
end MGAP4D

end
