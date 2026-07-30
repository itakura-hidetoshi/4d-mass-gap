import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputPairwiseExponentialContractionFullGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, two left trajectories driven by the same constant input contract at
    the full exact-gap rate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F_lim) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + F_lim) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F_lim hU0 hV0 hU hV

/-- On `Ω⊥`, two right trajectories have the identical full exact-gap contraction
    estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F_lim) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F_lim) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F_lim hU0 hV0 hU hV

end

end MathlibAnalytic
end MGAP4D
