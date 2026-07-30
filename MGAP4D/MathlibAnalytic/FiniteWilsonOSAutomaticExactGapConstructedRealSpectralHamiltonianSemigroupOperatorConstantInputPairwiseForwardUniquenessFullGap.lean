import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputPairwiseExponentialContractionFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left evolution is forward unique from a common
    initial operator under the same constant input. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_eq_of_sameInitial_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F_lim) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F_lim) r)
    (hAB : A = B) :
    U t = V t := by
  have hcontract :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_left
      D n t₀ t ht A B U V F_lim hU0 hV0 hU hV
  have hzero : ‖U t - V t‖ ≤ 0 := by
    simpa [hAB] using hcontract
  have hnorm : ‖U t - V t‖ = 0 := le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Constructed finite Wilson right evolution is forward unique from a common
    initial operator under the same constant input. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_eq_of_sameInitial_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F_lim) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F_lim) r)
    (hAB : A = B) :
    U t = V t := by
  have hcontract :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_right
      D n t₀ t ht A B U V F_lim hU0 hV0 hU hV
  have hzero : ‖U t - V t‖ ≤ 0 := by
    simpa [hAB] using hcontract
  have hnorm : ‖U t - V t‖ = 0 := le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end

end MathlibAnalytic
end MGAP4D
