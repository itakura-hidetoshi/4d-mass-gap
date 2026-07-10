import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedLowerBoundSubset
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Lower-bound ray factorization for the complete Yang--Mills direct bounded route.

The lower-bound subset package provides a positive witness `δ` such that every
nonzero spectral energy lies in the closed upper ray `{E | δ ≤ E}`.  This file
packages the next order-theoretic factorization: the same ray is contained in
the positive real half-line because `0 < δ`.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- A positive lower-bound ray is contained in the positive real half-line. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_lowerBoundRay_subset_positive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 < E} := by
  rcases euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_pointwise_lowerBound S with
    ⟨δ, hδ_pos, _hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hδE
    exact lt_of_lt_of_le hδ_pos hδE⟩

/-- The nonzero spectrum factors through a positive lower-bound ray. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_factorizes_through_positiveLowerBoundRay
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | δ ≤ E} ∧
      {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 < E} := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hE
    exact hδ_le E hE, by
    intro E hδE
    exact lt_of_lt_of_le hδ_pos hδE⟩

/-- A pointwise version of the lower-bound-ray factorization. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_pointwise_factorization
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E ∧ E ∈ {E : ℝ | δ ≤ E} ∧ E ∈ {E : ℝ | 0 < E} := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hE
    have hδE : δ ≤ E := hδ_le E hE
    exact ⟨hδE, hδE, lt_of_lt_of_le hδ_pos hδE⟩⟩

/-- The factorization package also recovers the existing positive-subset theorem. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_factorized_nonzeroSpectrum_subset_positive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
      {E : ℝ | 0 < E} := by
  intro E hE
  rcases euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_factorizes_through_positiveLowerBoundRay S with
    ⟨δ, _hδ_pos, hsubset_lower, hsubset_pos⟩
  exact hsubset_pos (hsubset_lower hE)

/-- Complete lower-bound-ray factorization package. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_lowerBoundRay_factorization_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      (∃ δ : ℝ, 0 < δ ∧
        S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
          {E : ℝ | δ ≤ E} ∧
        {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 < E}) ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | 0 < E} := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_factorizes_through_positiveLowerBoundRay S,
    euclideanYangMillsCompleteConstructionDirectBounded_factorized_nonzeroSpectrum_subset_positive S⟩

end

end MathlibAnalytic
end MGAP4D
