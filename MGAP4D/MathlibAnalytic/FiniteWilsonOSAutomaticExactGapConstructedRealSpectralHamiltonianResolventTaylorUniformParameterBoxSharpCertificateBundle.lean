import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorUniformParameterBoxSharpCertificateBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorSharpMinimalTruncationTheoryBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The single sharp Taylor degree attached to the worst corner of an exact-gap
finite Wilson parameter box. -/
noncomputable def finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
    (lambdaMax rMax epsilonMin : ℝ) : ℕ :=
  resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
    exactGapValueReal lambdaMax rMax epsilonMin

/-- Every exact-gap finite Wilson sharp degree in the parameter box is bounded
by the sharp degree at the worst corner. -/
theorem finiteWilsonExactGapResolventTaylorSharpTruncationOrder_le_parameterBoxWorstCorner
    {lambda lambdaMax r rMax epsilonMin epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hlambdaMax : lambdaMax < exactGapValueReal)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hrMaxlt : rMax < exactGapValueReal - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    (hepsilon : epsilonMin ≤ epsilon) :
    finiteWilsonExactGapResolventTaylorSharpTruncationOrder
        lambda r epsilon ≤
      finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
        lambdaMax rMax epsilonMin := by
  simpa [finiteWilsonExactGapResolventTaylorSharpTruncationOrder,
    finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder] using
    (resolventTaylorClosedBall_sharpTruncationOrder_le_parameterBoxWorstCorner
      (deltaMin := exactGapValueReal) (delta := exactGapValueReal)
      le_rfl hlambda hlambdaMax hr0 hr hrMaxlt hepsilonMin hepsilon)

/-- The worst-corner exact-gap finite Wilson degree is the actual maximum sharp
degree attained over the full center-radius-tolerance parameter box. -/
theorem finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder_isGreatest
    {lambdaMax rMax epsilonMin : ℝ}
    (hlambdaMax : lambdaMax < exactGapValueReal)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < exactGapValueReal - lambdaMax)
    (hepsilonMin : 0 < epsilonMin) :
    IsGreatest
      {N : ℕ |
        ∃ lambda r epsilon : ℝ,
          lambda ≤ lambdaMax ∧
          0 ≤ r ∧ r ≤ rMax ∧
          epsilonMin ≤ epsilon ∧
          N = finiteWilsonExactGapResolventTaylorSharpTruncationOrder
            lambda r epsilon}
      (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
        lambdaMax rMax epsilonMin) := by
  constructor
  · refine ⟨lambdaMax, rMax, epsilonMin, le_rfl, hrMax0, le_rfl,
      le_rfl, ?_⟩
    rfl
  · intro N hN
    rcases hN with
      ⟨lambda, r, epsilon, hlambda, hr0, hr, hepsilon, rfl⟩
    exact
      finiteWilsonExactGapResolventTaylorSharpTruncationOrder_le_parameterBoxWorstCorner
        hlambda hlambdaMax hr0 hr hrMaxlt hepsilonMin hepsilon

/-- Every degree above the worst-corner certificate controls operator-norm
Taylor remainders simultaneously for all constructed finite Wilson indices and
all centers, radii, tolerances, and spectral parameters in the box. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_allIndices_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambdaMax rMax epsilonMin : ℝ}
    (hlambdaMax : lambdaMax < exactGapValueReal)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < exactGapValueReal - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    {N : ℕ}
    (hN : finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
      lambdaMax rMax epsilonMin ≤ N)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda)‖ < epsilon := by
  simpa only [finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder,
    finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_family_of_worstCornerSharpTruncationOrder
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      (deltaMin := exactGapValueReal) le_rfl hlambdaMax hrMax0 hrMaxlt
      hepsilonMin hlambda hr0 hr hepsilon hN n mu hmu)

/-- The same worst-corner certificate controls every two-unit-ball matrix
element simultaneously for all constructed finite Wilson indices and all
parameters in the box. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_allIndices_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambdaMax rMax epsilonMin : ℝ}
    (hlambdaMax : lambdaMax < exactGapValueReal)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < exactGapValueReal - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    {N : ℕ}
    (hN : finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
      lambdaMax rMax epsilonMin ≤ N)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : D.StateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y)| < epsilon := by
  simpa only [finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder,
    finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_family_of_worstCornerSharpTruncationOrder
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      (deltaMin := exactGapValueReal) le_rfl hlambdaMax hrMax0 hrMaxlt
      hepsilonMin hlambda hr0 hr hepsilon hN n mu hmu x y hx hy)

/-- At the worst-corner sharp degree itself, every constructed finite Wilson
operator-norm Taylor remainder satisfies its requested tolerance throughout the
full parameter box. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_allIndices_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambdaMax rMax epsilonMin : ℝ}
    (hlambdaMax : lambdaMax < exactGapValueReal)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < exactGapValueReal - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda)‖ < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_allIndices_of_worstCornerSharpTruncationOrder
      D hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl n mu hmu

/-- At the worst-corner sharp degree itself, every constructed finite Wilson
matrix element on the two unit balls satisfies its requested tolerance
throughout the full parameter box. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_allIndices_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambdaMax rMax epsilonMin : ℝ}
    (hlambdaMax : lambdaMax < exactGapValueReal)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < exactGapValueReal - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : D.StateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y)| < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_allIndices_of_worstCornerSharpTruncationOrder
      D hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl n mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end
