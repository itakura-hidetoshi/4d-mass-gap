import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Positive nonzero-spectrum theorem for the complete Yang--Mills direct bounded
route.

The spectral downstream package exposes a positive lower-bound witness for the
nonzero spectrum.  This file performs the next elementary order-theoretic step:
from `0 < δ` and `δ ≤ E`, every nonzero spectral energy `E` is positive.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Every nonzero spectral energy is positive along the complete direct bounded
spectral downstream route. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∀ E : ℝ,
      E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
      0 < E := by
  intro E hE
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact lt_of_lt_of_le hδ_pos (hδ_le E hE)

/-- The lower-bound witness can be packaged together with positivity of every
nonzero spectral energy. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_positiveLowerBoundPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        0 < E ∧ δ ≤ E := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hE
    exact ⟨lt_of_lt_of_le hδ_pos (hδ_le E hE), hδ_le E hE⟩⟩

/-- Complete downstream positivity package: mass-gap predicate, positive exact
value, and positivity of every nonzero spectral energy. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      (∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        0 < E) ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ E : ℝ,
          E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
          0 < E ∧ δ ≤ E := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_positiveLowerBoundPackage S⟩

end

end MathlibAnalytic
end MGAP4D
