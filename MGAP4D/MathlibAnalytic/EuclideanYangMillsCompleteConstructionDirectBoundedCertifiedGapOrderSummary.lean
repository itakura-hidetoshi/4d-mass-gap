import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedCertifiedNonzeroSpectrumPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Certified gap-order summary for the complete Yang--Mills direct bounded route.

This summary layer intentionally bundles several downstream facts together:
positive exact gap value, nonzero exact gap value, positive nonzero-spectrum
infimum, nonzero infimum, exact-gap formula, and the certified lower-bound
witness package.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Certified gap-order summary combining exact-gap positivity, nonzeroness,
positive infimum, and the exact-gap formula. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_certifiedGapOrder_summary
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal ≠ 0 ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ≠ 0 ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGapValue_ne_zero S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_ne_zero S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S⟩

/-- Certified gap-order summary with a lower-bound witness attached. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_certifiedGapOrder_withLowerBoundWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ E ≠ 0 := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S,
    by
      intro E hE
      have hδE : δ ≤ E := hδ_le E hE
      have hpos : 0 < E := lt_of_lt_of_le hδ_pos hδE
      exact ⟨hδE, hpos, le_of_lt hpos, ne_of_gt hpos⟩⟩

/-- Full certified direct-bounded gap-order and nonzero-spectrum package. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_certifiedGapOrder_fullPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal ≠ 0 ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ≠ 0 ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))) ∧
      (∃ δ : ℝ, 0 < δ ∧
        S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
          {E : ℝ | δ ≤ E} ∧
        {E : ℝ | δ ≤ E} ⊆ {E : ℝ | 0 < E} ∧
        ∀ E : ℝ,
          E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
          δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ E ≠ 0 ∧ ¬ E < δ ∧ ¬ E ≤ 0) := by
  constructor
  · exact euclideanYangMillsCompleteConstructionDirectBounded_certifiedGapOrder_summary S
  · rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
      ⟨δ, hδ_pos, hδ_le⟩
    exact ⟨δ, hδ_pos, by
      intro E hE
      exact hδ_le E hE, by
      intro E hδE
      exact lt_of_lt_of_le hδ_pos hδE, by
      intro E hE
      have hδE : δ ≤ E := hδ_le E hE
      have hpos : 0 < E := lt_of_lt_of_le hδ_pos hδE
      exact ⟨hδE, hpos, le_of_lt hpos, ne_of_gt hpos, not_lt_of_ge hδE,
        not_le_of_gt hpos⟩⟩

end

end MathlibAnalytic
end MGAP4D
