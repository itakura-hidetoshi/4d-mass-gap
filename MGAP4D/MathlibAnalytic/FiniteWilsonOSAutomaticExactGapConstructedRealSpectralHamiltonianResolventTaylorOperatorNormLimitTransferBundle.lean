import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorOperatorNormLimitTransferBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorUniformParameterBoxSharpCertificateBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- Operator-norm value-and-derivative convergence data for the constructed
finite Wilson resolvent sequence. -/
abbrev FiniteWilsonConstructedResolventTaylorOperatorNormLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W) :=
  ContinuousLinearMapTaylorOperatorNormLimitData
    (fun n : ℕ =>
      finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)

/-- The constructed finite Wilson operator-norm resolvent limit is unique. -/
theorem finiteWilsonConstructedResolventTaylorOperatorNormLimitData_limit_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (L₁ L₂ : FiniteWilsonConstructedResolventTaylorOperatorNormLimitData D) :
    L₁.limitResolvent = L₂.limitResolvent :=
  ContinuousLinearMapTaylorOperatorNormLimitData.limitResolvent_unique L₁ L₂

/-- The exact-gap geometric Taylor envelope passes from every constructed
finite Wilson approximant to its operator-norm resolvent limit. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_sub_taylor_partialSum_norm_le_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (L : FiniteWilsonConstructedResolventTaylorOperatorNormLimitData D)
    {lambda r mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) :
    ‖L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N‖ ≤
      (r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹ := by
  change ContinuousLinearMapTaylorOperatorNormLimitData
    (fun n : ℕ =>
      orthonormalDiagonalHamiltonianResolvent
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) at L
  exact
    orthonormalDiagonalHamiltonianResolvent_limit_sub_taylor_partialSum_norm_le_closedBall
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      L hlambda hr0 hrlt hmu N

/-- One worst-corner Taylor degree controls the constructed finite Wilson
operator-norm resolvent limit throughout the full center-radius-tolerance box. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (L : FiniteWilsonConstructedResolventTaylorOperatorNormLimitData D)
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
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N‖ <
      epsilon := by
  change ContinuousLinearMapTaylorOperatorNormLimitData
    (fun n : ℕ =>
      orthonormalDiagonalHamiltonianResolvent
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) at L
  have hN' :
      resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
        exactGapValueReal lambdaMax rMax epsilonMin ≤ N := by
    simpa [finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder]
      using hN
  exact
    orthonormalDiagonalHamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      L (deltaMin := exactGapValueReal) le_rfl hlambdaMax hrMax0 hrMaxlt
      hepsilonMin hlambda hr0 hr hepsilon hN' mu hmu

/-- The same worst-corner degree controls all two-unit-ball real matrix elements
of the constructed finite Wilson operator-norm resolvent limit. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (L : FiniteWilsonConstructedResolventTaylorOperatorNormLimitData D)
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
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : D.StateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N) y)| <
      epsilon := by
  change ContinuousLinearMapTaylorOperatorNormLimitData
    (fun n : ℕ =>
      orthonormalDiagonalHamiltonianResolvent
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) at L
  have hN' :
      resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
        exactGapValueReal lambdaMax rMax epsilonMin ≤ N := by
    simpa [finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder]
      using hN
  exact
    orthonormalDiagonalHamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      L (deltaMin := exactGapValueReal) le_rfl hlambdaMax hrMax0 hrMaxlt
      hepsilonMin hlambda hr0 hr hepsilon hN' mu hmu x y hx hy

/-- At the exact-gap worst-corner sharp degree itself, the constructed finite
Wilson operator-norm resolvent limit satisfies every tolerance in the box. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (L : FiniteWilsonConstructedResolventTaylorOperatorNormLimitData D)
    {lambdaMax rMax epsilonMin : ℝ}
    (hlambdaMax : lambdaMax < exactGapValueReal)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < exactGapValueReal - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin)‖ < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      D L hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl mu hmu

/-- At the exact-gap worst-corner sharp degree itself, all unit-ball matrix
elements of the constructed finite Wilson limit remainder satisfy tolerance. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (L : FiniteWilsonConstructedResolventTaylorOperatorNormLimitData D)
    {lambdaMax rMax epsilonMin : ℝ}
    (hlambdaMax : lambdaMax < exactGapValueReal)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < exactGapValueReal - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : D.StateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin)) y)| < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      D L hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end