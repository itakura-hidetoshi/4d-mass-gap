import MGAP4D.MathlibAnalytic.WightmanOSConnectedCorrelationSpectralGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Non-atomic correlation-to-gap input.

For an energy `E` in the spectral support and a small `ε > 0`, `localWeight E ε`
represents positive spectral mass in a neighborhood whose energies are bounded
above by `E + ε`.  This is the correct support-level replacement for requiring
positive mass of the singleton `{E}`. -/
structure ExplicitWightmanOSConnectedCorrelationOpenSupportBounds
    (Δ : ℝ) where
  correlation : ℝ → ℝ
  decayConstant : ℝ
  decayConstant_nonneg : 0 ≤ decayConstant
  spectralSupport : Set ℝ
  gapPositive : 0 < Δ
  localWeight : ℝ → ℝ → ℝ
  localWeight_pos :
    ∀ {E : ℝ}, E ∈ spectralSupport →
      ∀ {ε : ℝ}, 0 < ε → E + ε < Δ →
        0 < localWeight E ε
  localLaplaceLowerBound :
    ∀ {E : ℝ}, E ∈ spectralSupport →
      ∀ {ε : ℝ}, 0 < ε → E + ε < Δ →
        ∀ t : ℝ, 0 ≤ t →
          localWeight E ε * Real.exp (-(E + ε) * t) ≤
            correlation t
  connectedCorrelationExponentialUpperBound :
    ∀ t : ℝ, 0 ≤ t →
      correlation t ≤ decayConstant * Real.exp (-Δ * t)

/-- Exponential decay excludes every spectral-support point below `Δ` without
assuming that any singleton carries positive measure. -/
theorem connected_correlation_open_support_subset_Ici
    {Δ : ℝ}
    (B : ExplicitWightmanOSConnectedCorrelationOpenSupportBounds Δ) :
    B.spectralSupport ⊆ Set.Ici Δ := by
  intro E hE
  by_contra hNotLower
  have hEΔ : E < Δ := lt_of_not_ge hNotLower
  let ε : ℝ := (Δ - E) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hSubgap : E + ε < Δ := by
    dsimp [ε]
    linarith
  have hWeight : 0 < B.localWeight E ε :=
    B.localWeight_pos hE hε hSubgap
  obtain ⟨t, ht, hSeparation⟩ :=
    exists_subgap_exponential_separation
      hWeight B.decayConstant_nonneg hSubgap
  have hLower :=
    B.localLaplaceLowerBound hE hε hSubgap t ht
  have hUpper :=
    B.connectedCorrelationExponentialUpperBound t ht
  linarith

/-- Pointwise form of the non-atomic spectral-support lower bound. -/
theorem connected_correlation_open_support_energy_lower_bound
    {Δ E : ℝ}
    (B : ExplicitWightmanOSConnectedCorrelationOpenSupportBounds Δ)
    (hE : E ∈ B.spectralSupport) :
    Δ ≤ E :=
  connected_correlation_open_support_subset_Ici B hE

/-- The singleton-weight route is only a pure-point specialization.  The main
support theorem above does not require `μ({E}) > 0` or an eigenvector at `E`. -/
def HasPurePointSpectralSupport
    (support pointSpectrum : Set ℝ) : Prop :=
  support = pointSpectrum

end

end MathlibAnalytic
end MGAP4D
