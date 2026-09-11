import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedNonzeroSpectrumPositive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Positive gap-infimum theorem for the complete Yang--Mills direct bounded route.

The spectral downstream package already exposes both the exact-gap formula and
positivity of `exactGapValueReal`.  This file rewrites along the exact-gap formula
to prove that the infimum of the nonzero spectrum is itself positive.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- The infimum of the nonzero spectrum is positive along the complete direct
bounded route. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  rw [← euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S]
  exact euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S

/-- The exact gap value is nonzero. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactGapValue_ne_zero
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal ≠ 0 := by
  exact ne_of_gt
    (euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S)

/-- The nonzero-spectrum infimum is nonzero. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_ne_zero
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ≠ 0 := by
  exact ne_of_gt
    (euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S)

/-- Package the positive exact gap value with the positive nonzero-spectrum
infimum and the exact-gap formula. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    0 < exactGapValueReal ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S⟩

/-- Complete positivity package: mass-gap predicate, positive exact value,
positive infimum, and positivity of every nonzero spectral energy. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      (∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        0 < E) ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S⟩

end

end MathlibAnalytic
end MGAP4D
