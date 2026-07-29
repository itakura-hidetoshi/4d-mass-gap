import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelUniformForcingLongTimeISS
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingGain

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- Constructed finite Wilson left forced evolution has long-time gain at most the
uniform forcing magnitude divided by the exact spectral gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_limsup_norm_le_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    Filter.limsup (fun t : ℝ => ‖U t‖) atTop ≤ M / exactGapValueReal := by
  have hM : 0 ≤ M :=
    le_trans (norm_nonneg (F t₀)) (hFM t₀ le_rfl)
  have hbound :
      ∀ᶠ t : ℝ in atTop,
        ‖U t‖ ≤
          Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
            M / exactGapValueReal := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with t ht
    exact
      finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
        D n t₀ t ht A F U M hM hF (fun s hs => hFM s hs.1) hU0 hU
  exact
    limsup_norm_le_of_eventually_le_exp_transient
      U t₀ exactGapValueReal ‖A‖ (M / exactGapValueReal)
      exactGapValueReal_pos hbound

/-- Constructed finite Wilson right forced evolution has the same long-time exact-
gap gain, with no commutation hypothesis on the data. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_limsup_norm_le_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    Filter.limsup (fun t : ℝ => ‖U t‖) atTop ≤ M / exactGapValueReal := by
  have hM : 0 ≤ M :=
    le_trans (norm_nonneg (F t₀)) (hFM t₀ le_rfl)
  have hbound :
      ∀ᶠ t : ℝ in atTop,
        ‖U t‖ ≤
          Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
            M / exactGapValueReal := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with t ht
    exact
      finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
        D n t₀ t ht A F U M hM hF (fun s hs => hFM s hs.1) hU0 hU
  exact
    limsup_norm_le_of_eventually_le_exp_transient
      U t₀ exactGapValueReal ‖A‖ (M / exactGapValueReal)
      exactGapValueReal_pos hbound

end

end MathlibAnalytic
end MGAP4D
