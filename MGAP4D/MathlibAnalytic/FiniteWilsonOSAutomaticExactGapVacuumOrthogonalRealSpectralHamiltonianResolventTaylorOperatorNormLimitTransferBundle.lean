import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorOperatorNormLimitTransferBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventTaylorUniformParameterBoxSharpCertificateBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- Operator-norm value-and-derivative convergence data for the finite Wilson
vacuum-orthogonal resolvent sequence. -/
abbrev FiniteWilsonVacuumOrthogonalResolventTaylorOperatorNormLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W) :=
  ContinuousLinearMapTaylorOperatorNormLimitData
    (fun n : ℕ =>
      finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)

/-- The vacuum-orthogonal finite Wilson operator-norm resolvent limit is unique. -/
theorem finiteWilsonVacuumOrthogonalResolventTaylorOperatorNormLimitData_limit_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (L₁ L₂ : FiniteWilsonVacuumOrthogonalResolventTaylorOperatorNormLimitData D) :
    L₁.limitResolvent = L₂.limitResolvent :=
  ContinuousLinearMapTaylorOperatorNormLimitData.limitResolvent_unique L₁ L₂

/-- The exact-gap geometric Taylor envelope passes to every operator-norm limit
of the finite Wilson vacuum-orthogonal resolvent sequence. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_sub_taylor_partialSum_norm_le_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (L : FiniteWilsonVacuumOrthogonalResolventTaylorOperatorNormLimitData D)
    {lambda r mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) :
    ‖L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N‖ ≤
      (r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹ := by
  change FiniteWilsonConstructedResolventTaylorOperatorNormLimitData
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData at L
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_sub_taylor_partialSum_norm_le_closedBall
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      L hlambda hr0 hrlt hmu N

/-- One worst-corner degree controls the operator-norm vacuum-orthogonal limit
resolvent throughout the full exact-gap parameter box. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (L : FiniteWilsonVacuumOrthogonalResolventTaylorOperatorNormLimitData D)
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
  change FiniteWilsonConstructedResolventTaylorOperatorNormLimitData
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData at L
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      L hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      hN mu hmu

/-- The same worst-corner degree controls every two-unit-ball real matrix
element of the vacuum-orthogonal operator-norm limit resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (L : FiniteWilsonVacuumOrthogonalResolventTaylorOperatorNormLimitData D)
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
    (x y : D.gapData.ExcitedStateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N) y)| <
      epsilon := by
  change FiniteWilsonConstructedResolventTaylorOperatorNormLimitData
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData at L
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      L hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      hN mu hmu x y hx hy

/-- At the worst-corner sharp degree itself, the vacuum-orthogonal limit
resolvent satisfies every operator-norm tolerance in the parameter box. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (L : FiniteWilsonVacuumOrthogonalResolventTaylorOperatorNormLimitData D)
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
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      D L hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl mu hmu

/-- At the worst-corner sharp degree itself, all vacuum-orthogonal unit-ball
matrix elements satisfy every requested tolerance in the parameter box. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (L : FiniteWilsonVacuumOrthogonalResolventTaylorOperatorNormLimitData D)
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
    (x y : D.gapData.ExcitedStateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin)) y)| < epsilon := by
  exact
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      D L hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end