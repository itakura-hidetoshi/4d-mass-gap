import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorExplicitLogCeilTruncationOrderBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorOperatorNormMatrixElementDualityBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The explicit logarithmic-ceiling Taylor order for the exact finite Wilson
gap and a closed parameter ball. -/
noncomputable def finiteWilsonExactGapResolventTaylorExplicitTruncationOrder
    (lambda r epsilon : ℝ) : ℕ :=
  resolventTaylorClosedBall_explicitTruncationOrder
    exactGapValueReal lambda r epsilon

/-- The finite Wilson explicit Taylor order is positive. -/
theorem finiteWilsonExactGapResolventTaylorExplicitTruncationOrder_pos
    (lambda r epsilon : ℝ) :
    0 < finiteWilsonExactGapResolventTaylorExplicitTruncationOrder
      lambda r epsilon := by
  exact resolventTaylorClosedBall_explicitTruncationOrder_pos _ _ _ _

/-- Every degree at or above the explicit order controls the operator-norm
Taylor remainder simultaneously for all constructed finite Wilson indices. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_allIndices_of_explicitTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : finiteWilsonExactGapResolventTaylorExplicitTruncationOrder
      lambda r epsilon ≤ N)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda)‖ < epsilon := by
  simpa only [finiteWilsonExactGapResolventTaylorExplicitTruncationOrder,
    finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_family_of_explicitTruncationOrder
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hepsilon hN n mu hmu)

/-- The same explicit order controls every two-unit-ball matrix element for all
constructed finite Wilson indices. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_allIndices_of_explicitTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : finiteWilsonExactGapResolventTaylorExplicitTruncationOrder
      lambda r epsilon ≤ N)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : D.StateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y)| < epsilon := by
  simpa only [finiteWilsonExactGapResolventTaylorExplicitTruncationOrder,
    finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_family_of_explicitTruncationOrder
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hepsilon hN n mu hmu x y hx hy)

/-- At the explicit order itself, all constructed finite Wilson operator-norm
Taylor errors are strictly below `epsilon`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_allIndices_at_explicitTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range
          (finiteWilsonExactGapResolventTaylorExplicitTruncationOrder
            lambda r epsilon),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda)‖ < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_allIndices_of_explicitTruncationOrder
      D hlambda hr0 hrlt hepsilon le_rfl n mu hmu

/-- At the explicit order itself, all constructed finite Wilson two-unit-ball
matrix elements are strictly below `epsilon`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_allIndices_at_explicitTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : D.StateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range
          (finiteWilsonExactGapResolventTaylorExplicitTruncationOrder
            lambda r epsilon),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y)| < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_allIndices_of_explicitTruncationOrder
      D hlambda hr0 hrlt hepsilon le_rfl n mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end