import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorStrongLimitUpgradeBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorOperatorNormLimitTransferBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- Statewise value-and-derivative strong-limit data for the constructed finite
Wilson resolvent sequence. -/
abbrev FiniteWilsonConstructedResolventTaylorStrongLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W) :=
  ContinuousLinearMapTaylorStrongLimitData
    (fun n : ℕ =>
      finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)

/-- Finite-dimensionality upgrades constructed finite Wilson strong-limit data
to operator-norm value-and-derivative convergence. -/
noncomputable def FiniteWilsonConstructedResolventTaylorStrongLimitData.toOperatorNormLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W}
    (S : FiniteWilsonConstructedResolventTaylorStrongLimitData D) :
    FiniteWilsonConstructedResolventTaylorOperatorNormLimitData D :=
  ContinuousLinearMapTaylorStrongLimitData.toOperatorNormLimitData S

/-- The constructed finite Wilson strong resolvent Taylor limit is unique. -/
theorem finiteWilsonConstructedResolventTaylorStrongLimitData_limit_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (S₁ S₂ : FiniteWilsonConstructedResolventTaylorStrongLimitData D) :
    S₁.limitResolvent = S₂.limitResolvent :=
  ContinuousLinearMapTaylorStrongLimitData.limitResolvent_unique S₁ S₂

/-- The exact spectral gap supplies the same resolvent norm bound for the
constructed finite Wilson strong limit. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_norm_le_inv_sub
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (S : FiniteWilsonConstructedResolventTaylorStrongLimitData D)
    {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ‖S.limitResolvent lambda‖ ≤ (exactGapValueReal - lambda)⁻¹ := by
  change ContinuousLinearMapTaylorStrongLimitData
    (fun n : ℕ =>
      orthonormalDiagonalHamiltonianResolvent
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) at S
  exact
    orthonormalDiagonalHamiltonianResolvent_strongLimit_norm_le_inv_sub
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      S hlambda

/-- All factorial distance-to-gap derivative bounds pass to the constructed
finite Wilson strong Taylor limit. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_iteratedDeriv_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (S : FiniteWilsonConstructedResolventTaylorStrongLimitData D)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ‖iteratedDeriv k S.limitResolvent lambda‖ ≤
      (k.factorial : ℝ) * ((exactGapValueReal - lambda)⁻¹) ^ (k + 1) := by
  change ContinuousLinearMapTaylorStrongLimitData
    (fun n : ℕ =>
      orthonormalDiagonalHamiltonianResolvent
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) at S
  exact
    orthonormalDiagonalHamiltonianResolvent_strongLimit_iteratedDeriv_norm_le
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      S k hlambda

/-- The exact-gap geometric closed-ball Taylor envelope passes from all
constructed finite Wilson approximants to their strong limit. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_sub_taylor_partialSum_norm_le_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (S : FiniteWilsonConstructedResolventTaylorStrongLimitData D)
    {lambda r mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) :
    ‖S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu N‖ ≤
      (r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_sub_taylor_partialSum_norm_le_closedBall
      D S.toOperatorNormLimitData hlambda hr0 hrlt hmu N

/-- One exact-gap worst-corner degree controls the constructed finite Wilson
strong limit throughout the full center-radius-tolerance box. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (S : FiniteWilsonConstructedResolventTaylorStrongLimitData D)
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
    ‖S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu N‖ <
      epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      D S.toOperatorNormLimitData hlambdaMax hrMax0 hrMaxlt hepsilonMin
      hlambda hr0 hr hepsilon hN mu hmu

/-- The constructed finite Wilson strong-limit certificate controls all real
matrix elements on the two closed unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (S : FiniteWilsonConstructedResolventTaylorStrongLimitData D)
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
      ((S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu N) y)| <
      epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      D S.toOperatorNormLimitData hlambdaMax hrMax0 hrMaxlt hepsilonMin
      hlambda hr0 hr hepsilon hN mu hmu x y hx hy

/-- At the exact-gap worst-corner degree itself, the constructed finite Wilson
strong limit satisfies every operator-norm tolerance in the box. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_taylor_operatorNorm_error_lt_parameterBox_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (S : FiniteWilsonConstructedResolventTaylorStrongLimitData D)
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
    ‖S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin)‖ < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      D S hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl mu hmu

/-- At the exact-gap worst-corner degree itself, all unit-ball matrix elements
of the constructed finite Wilson strong-limit remainder satisfy tolerance. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (S : FiniteWilsonConstructedResolventTaylorStrongLimitData D)
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
      ((S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin)) y)| < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      D S hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end