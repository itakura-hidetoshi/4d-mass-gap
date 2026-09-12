import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorUniformParameterBoxSharpCertificateBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventTaylorSharpMinimalTruncationTheoryBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- Every degree above the worst-corner certificate controls operator-norm
Taylor remainders simultaneously for all finite Wilson `Ω⊥` indices and all
centers, radii, tolerances, and spectral parameters in the box. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_allIndices_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
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
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
            lambda)‖ < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_allIndices_of_worstCornerSharpTruncationOrder
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      hN n mu hmu

/-- The same worst-corner certificate controls every two-unit-ball matrix
element simultaneously for all finite Wilson `Ω⊥` indices and all parameters
in the box. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_allIndices_of_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
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
    (x y : D.gapData.ExcitedStateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
            lambda) y)| < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_allIndices_of_worstCornerSharpTruncationOrder
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      hN n mu hmu x y hx hy

/-- At the worst-corner sharp degree itself, every finite Wilson `Ω⊥`
operator-norm Taylor remainder satisfies its requested tolerance throughout the
full parameter box. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_allIndices_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
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
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
            lambda)‖ < epsilon := by
  exact
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_allIndices_of_worstCornerSharpTruncationOrder
      D hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl n mu hmu

/-- At the worst-corner sharp degree itself, every finite Wilson `Ω⊥` matrix
element on the two unit balls satisfies its requested tolerance throughout the
full parameter box. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_allIndices_at_worstCornerSharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
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
    (x y : D.gapData.ExcitedStateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range
          (finiteWilsonExactGapResolventTaylorParameterBoxWorstCornerSharpTruncationOrder
            lambdaMax rMax epsilonMin),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
            lambda) y)| < epsilon := by
  exact
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_allIndices_of_worstCornerSharpTruncationOrder
      D hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon
      le_rfl n mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end
