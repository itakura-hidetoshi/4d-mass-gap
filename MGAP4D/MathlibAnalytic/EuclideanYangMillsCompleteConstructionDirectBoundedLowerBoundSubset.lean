import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedNonzeroSpectrumOrder
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Lower-bound subset package for the complete Yang--Mills direct bounded route.

The spectral downstream package provides a positive lower-bound witness for the
nonzero spectrum.  This file packages that witness as a set inclusion into a
closed lower half-line and exposes the corresponding exclusion of energies below
the witness.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- There is a positive lower-bound witness whose closed upper ray contains the
nonzero spectrum. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_lowerBoundRay
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | δ ≤ E} := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hE
    exact hδ_le E hE⟩

/-- There is a positive lower-bound witness below every nonzero spectral energy. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_pointwise_lowerBound
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S

/-- There is a positive lower-bound witness such that no nonzero spectral energy
lies strictly below it. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_not_below_lowerBound
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        ¬ E < δ := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hE
    exact not_lt_of_ge (hδ_le E hE)⟩

/-- The lower-bound witness can be packaged with positivity and nonnegativity of
each nonzero spectral energy. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_lowerBound_order_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ ¬ E < δ := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hE
    have hle : δ ≤ E := hδ_le E hE
    have hpos : 0 < E :=
      euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S E hE
    exact ⟨hle, hpos, le_of_lt hpos, not_lt_of_ge hle⟩⟩

/-- Complete lower-bound subset package for downstream use. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_lowerBound_subset_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      (∃ δ : ℝ, 0 < δ ∧
        S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
          {E : ℝ | δ ≤ E}) ∧
      (∃ δ : ℝ, 0 < δ ∧
        ∀ E : ℝ,
          E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
          ¬ E < δ) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_lowerBoundRay S,
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_not_below_lowerBound S⟩

end

end MathlibAnalytic
end MGAP4D
