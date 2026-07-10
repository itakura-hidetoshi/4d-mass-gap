import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedNonzeroSpectrumSubsetPositive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Order-theoretic nonzero-spectrum package for the complete Yang--Mills direct
bounded route.

The previous set-theoretic layer proves that the nonzero spectrum is contained
in the positive real half-line.  This file exposes the immediate order-theoretic
consequences as reusable downstream theorems: nonnegativity, exclusion of the
nonpositive half-line, and membership in the positive set.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Every nonzero spectral energy is nonnegative. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_nonnegative
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∀ E : ℝ,
      E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
      0 ≤ E := by
  intro E hE
  exact le_of_lt
    (euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S E hE)

/-- No nonzero spectral energy is nonpositive. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_not_nonpositive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∀ E : ℝ,
      E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
      ¬ E ≤ 0 := by
  intro E hE
  exact not_le_of_gt
    (euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S E hE)

/-- Every nonzero spectral energy is a member of the positive real set. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_mem_positiveSet
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∀ E : ℝ,
      E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
      E ∈ {E : ℝ | 0 < E} := by
  intro E hE
  exact euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S E hE

/-- The nonzero spectrum is contained in the nonnegative real half-line. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_nonnegative
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
      {E : ℝ | 0 ≤ E} := by
  intro E hE
  exact euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_nonnegative S E hE

/-- The nonzero spectrum avoids the nonpositive real half-line. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_not_mem_nonpositiveSet
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∀ E : ℝ,
      E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
      E ∉ {E : ℝ | E ≤ 0} := by
  intro E hE hnonpos
  exact
    (euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_not_nonpositive S E hE)
      hnonpos

/-- Order package for a member of the nonzero spectrum. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_order_package
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    {E : ℝ}
    (hE : E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) :
    0 < E ∧ 0 ≤ E ∧ E ≠ 0 ∧ ¬ E ≤ 0 ∧ E ∈ {E : ℝ | 0 < E} := by
  have hpos : 0 < E :=
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S E hE
  exact ⟨hpos, le_of_lt hpos, ne_of_gt hpos, not_le_of_gt hpos, hpos⟩

/-- Complete order-theoretic nonzero-spectrum package. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_order_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | 0 < E} ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        {E : ℝ | 0 ≤ E} ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        0 < E ∧ 0 ≤ E ∧ E ≠ 0 ∧ ¬ E ≤ 0 := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_nonnegative S,
    by
      intro E hE
      have hpos : 0 < E :=
        euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_positive S E hE
      exact ⟨hpos, le_of_lt hpos, ne_of_gt hpos, not_le_of_gt hpos⟩⟩

end

end MathlibAnalytic
end MGAP4D
