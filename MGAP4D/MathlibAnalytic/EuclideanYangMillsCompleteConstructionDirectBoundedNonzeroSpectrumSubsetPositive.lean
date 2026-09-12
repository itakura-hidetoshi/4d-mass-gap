import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedGapInfimumPositive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Set-theoretic positive nonzero-spectrum package for the complete Yang--Mills
direct bounded route.

The previous proof layer shows that every member of the nonzero spectrum is
positive.  This file packages that fact as a subset theorem and exposes the
component projections for downstream callers: membership in the original energy
spectrum, nonzeroness, and strict positivity.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- The nonzero spectrum is contained in the positive real half-line. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_positive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
      {E : ℝ | 0 < E} := by
  intro E hE
  exact euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S E hE

/-- A member of the nonzero spectrum is an energy-spectrum member, is nonzero,
and is positive. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_member_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    {E : ℝ}
    (hE : E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) :
    E ∈ S.definitionBridge.spine.model.energySpectrum ∧ E ≠ 0 ∧ 0 < E := by
  have hpos : 0 < E :=
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S E hE
  exact ⟨hE.1, ne_of_gt hpos, hpos⟩

/-- Zero is not a member of the nonzero spectrum. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_zero_not_mem_nonzeroSpectrum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (0 : ℝ) ∉ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) := by
  intro h0
  exact h0.2 (by simp)

/-- Every member of the nonzero spectrum is nonzero. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_member_ne_zero
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∀ E : ℝ,
      E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
      E ≠ 0 := by
  intro E hE
  exact (euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_member_package S hE).2.1

/-- Complete set-theoretic package for the positive nonzero spectrum. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_positive_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | 0 < E} ∧
      (0 : ℝ) ∉ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        E ∈ S.definitionBridge.spine.model.energySpectrum ∧ E ≠ 0 ∧ 0 < E := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_zero_not_mem_nonzeroSpectrum S,
    by
      intro E hE
      exact euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_member_package S hE⟩

end

end MathlibAnalytic
end MGAP4D
