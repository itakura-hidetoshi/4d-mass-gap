import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorStrongLimitUpgradeBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventTaylorOperatorNormLimitTransferBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- Statewise value-and-derivative strong-limit data for the finite Wilson
vacuum-orthogonal resolvent sequence. -/
abbrev FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W) :=
  ContinuousLinearMapTaylorStrongLimitData
    (fun n : ℕ =>
      finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)

/-- Finite-dimensionality upgrades vacuum-orthogonal strong-limit data to the
operator-norm convergence package. -/
noncomputable def FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData.toOperatorNormLimitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W}
    (S : FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData D) :
    FiniteWilsonVacuumOrthogonalResolventTaylorOperatorNormLimitData D :=
  ContinuousLinearMapTaylorStrongLimitData.toOperatorNormLimitData S

/-- The finite Wilson vacuum-orthogonal strong resolvent Taylor limit is unique. -/
theorem finiteWilsonVacuumOrthogonalResolventTaylorStrongLimitData_limit_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (S₁ S₂ : FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData D) :
    S₁.limitResolvent = S₂.limitResolvent :=
  ContinuousLinearMapTaylorStrongLimitData.limitResolvent_unique S₁ S₂

/-- The exact gap supplies the same resolvent norm bound on the strong limit in
`Ω⊥`. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_strongLimit_norm_le_inv_sub
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (S : FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData D)
    {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ‖S.limitResolvent lambda‖ ≤ (exactGapValueReal - lambda)⁻¹ := by
  change FiniteWilsonConstructedResolventTaylorStrongLimitData
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData at S
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_norm_le_inv_sub
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData S hlambda

/-- Every exact factorial distance-to-gap derivative bound passes to the
vacuum-orthogonal strong Taylor limit. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_strongLimit_iteratedDeriv_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (S : FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData D)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ‖iteratedDeriv k S.limitResolvent lambda‖ ≤
      (k.factorial : ℝ) * ((exactGapValueReal - lambda)⁻¹) ^ (k + 1) := by
  change FiniteWilsonConstructedResolventTaylorStrongLimitData
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData at S
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_strongLimit_iteratedDeriv_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData S k hlambda

/-- The exact-gap closed-ball geometric Taylor envelope passes to the
vacuum-orthogonal strong limit. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_strongLimit_sub_taylor_partialSum_norm_le_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (S : FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData D)
    {lambda r mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) :
    ‖S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu N‖ ≤
      (r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹ := by
  exact
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_sub_taylor_partialSum_norm_le_closedBall
      D S.toOperatorNormLimitData hlambda hr0 hrlt hmu N

/-- One exact-gap worst-corner degree controls the vacuum-orthogonal strong
limit throughout the full center-radius-tolerance parameter box. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_strongLimit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (S : FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData D)
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
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      D S.toOperatorNormLimitData hlambdaMax hrMax0 hrMaxlt hepsilonMin
      hlambda hr0 hr hepsilon hN mu hmu

/-- The vacuum-orthogonal strong-limit certificate controls all real matrix
elements on the two closed unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_strongLimit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (S : FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData D)
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
      ((S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu N) y)| <
      epsilon := by
  exact
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      D S.toOperatorNormLimitData hlambdaMax hrMax0 hrMaxlt hepsilonMin
      hlambda hr0 hr hepsilon hN mu hmu x y hx hy

/-- At the exact-gap worst-corner degree itself, the vacuum-orthogonal strong
limit satisfies every operator-norm tolerance in the parameter box. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_strongLimit_taylor_operatorNorm_error_lt_parameterBox_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (S : FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData D)
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
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_strongLimit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      D S hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl mu hmu

/-- At the exact-gap worst-corner degree itself, all vacuum-orthogonal unit-ball
matrix elements of the strong-limit remainder satisfy tolerance. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_strongLimit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (S : FiniteWilsonVacuumOrthogonalResolventTaylorStrongLimitData D)
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
      ((S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin)) y)| < epsilon := by
  exact
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_strongLimit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      D S hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end