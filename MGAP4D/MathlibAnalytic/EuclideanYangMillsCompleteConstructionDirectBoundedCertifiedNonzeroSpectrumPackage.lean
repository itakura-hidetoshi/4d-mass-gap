import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedLowerBoundRayFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Certified nonzero-spectrum package for the complete Yang--Mills direct bounded
route.

This file intentionally advances by a larger package step.  It combines the
positive lower-bound witness, lower-bound ray factorization, positive and
nonnegative order consequences, nonzeroness, and exclusion of the nonpositive
half-line into downstream-ready theorem packages.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- A single positive witness controls all pointwise order facts for each
nonzero spectral energy. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_certifiedNonzeroSpectrum_pointwise_order
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ E ≠ 0 ∧ ¬ E < δ ∧ ¬ E ≤ 0 := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hE
    have hδE : δ ≤ E := hδ_le E hE
    have hpos : 0 < E := lt_of_lt_of_le hδ_pos hδE
    exact ⟨hδE, hpos, le_of_lt hpos, ne_of_gt hpos, not_lt_of_ge hδE,
      not_le_of_gt hpos⟩⟩

/-- A single positive witness gives the full subset chain from the nonzero
spectrum through its closed lower-bound ray into the positive and nonnegative
half-lines. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_certifiedNonzeroSpectrum_subset_chain
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | δ ≤ E} ∧
      {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 < E} ∧
      {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 ≤ E} ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | 0 < E} ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | 0 ≤ E} := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  have hray_pos : {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 < E} := by
    intro E hδE
    exact lt_of_lt_of_le hδ_pos hδE
  have hray_nonneg : {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 ≤ E} := by
    intro E hδE
    exact le_of_lt (lt_of_lt_of_le hδ_pos hδE)
  have hspectrum_ray :
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | δ ≤ E} := by
    intro E hE
    exact hδ_le E hE
  exact ⟨δ, hδ_pos, hspectrum_ray, hray_pos, hray_nonneg,
    by
      intro E hE
      exact hray_pos (hspectrum_ray hE),
    by
      intro E hE
      exact hray_nonneg (hspectrum_ray hE)⟩

/-- The certified witness packages lower-bound, positivity, nonnegativity,
nonzeroness, and both exclusion statements for every nonzero spectral energy. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_certifiedNonzeroSpectrum_member_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        E ∈ S.definitionBridge.spine.model.energySpectrum ∧
          δ ≤ E ∧
          0 < E ∧
          0 ≤ E ∧
          E ≠ 0 ∧
          E ∈ {E : ℝ | δ ≤ E} ∧
          E ∈ {E : ℝ | 0 < E} ∧
          E ∈ {E : ℝ | 0 ≤ E} ∧
          ¬ E < δ ∧
          ¬ E ≤ 0 := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hE
    have hδE : δ ≤ E := hδ_le E hE
    have hpos : 0 < E := lt_of_lt_of_le hδ_pos hδE
    exact ⟨hE.1, hδE, hpos, le_of_lt hpos, ne_of_gt hpos, hδE, hpos,
      le_of_lt hpos, not_lt_of_ge hδE, not_le_of_gt hpos⟩⟩

/-- Certified nonzero-spectrum package including mass-gap predicate, exact-gap
positivity, positive gap infimum, and the witness-based pointwise package. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_certifiedNonzeroSpectrum_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      (∃ δ : ℝ, 0 < δ ∧
        S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
          {E : ℝ | δ ≤ E} ∧
        {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 < E}) ∧
      (∃ δ : ℝ, 0 < δ ∧
        ∀ E : ℝ,
          E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
          δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ E ≠ 0 ∧ ¬ E < δ ∧ ¬ E ≤ 0) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S,
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_factorizes_through_positiveLowerBoundRay S,
    euclideanYangMillsCompleteConstructionDirectBounded_certifiedNonzeroSpectrum_pointwise_order S⟩

end

end MathlibAnalytic
end MGAP4D
