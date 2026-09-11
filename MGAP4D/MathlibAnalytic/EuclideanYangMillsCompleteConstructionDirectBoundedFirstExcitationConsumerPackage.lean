import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedCertifiedGapOrderSummary
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
First-excitation consumer package for the complete Yang--Mills direct bounded
route.

This package attaches the first-excitation spectral witness to the certified
gap-order and lower-bound witness facts produced by the direct bounded route.
It is a downstream consumer layer, not a new spectral theorem.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Certified gap facts together with the first-excitation spectral witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_certifiedGapPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      (∃ ψ : S.definitionBridge.spine.model.H,
        ψ ∈ S.definitionBridge.spine.model.spectralPVM
          ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_firstExcitationWitness S⟩

/-- A lower-bound witness and a first-excitation spectral witness in one package. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_lowerBound_firstExcitation_witnessPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E) ∧
      (∃ ψ : S.definitionBridge.spine.model.H,
        ψ ∈ S.definitionBridge.spine.model.spectralPVM
          ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_firstExcitationWitness S⟩

/-- A thin lower-bound order witness for consumers that only need the pointwise
order consequences. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_lowerBound_orderWitnessConsumer
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ E ≠ 0 := by
  rcases euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_lowerBound S with
    ⟨δ, hδ_pos, hδ_le⟩
  exact ⟨δ, hδ_pos, by
    intro E hE
    have hδE : δ ≤ E := hδ_le E hE
    have hpos : 0 < E := lt_of_lt_of_le hδ_pos hδE
    exact ⟨hδE, hpos, le_of_lt hpos, ne_of_gt hpos⟩⟩

/-- A single downstream package containing mass-gap, exact gap, lower-bound, and
first-excitation witnesses. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_fullConsumerPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal ≠ 0 ∧
      0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      (∃ δ : ℝ, 0 < δ ∧
        ∀ E : ℝ,
          E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
          δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ E ≠ 0) ∧
      (∃ ψ : S.definitionBridge.spine.model.H,
        ψ ∈ S.definitionBridge.spine.model.spectralPVM
          ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_positiveGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGapValue_ne_zero S,
    euclideanYangMillsCompleteConstructionDirectBounded_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_gapFormula S,
    euclideanYangMillsCompleteConstructionDirectBounded_lowerBound_orderWitnessConsumer S,
    euclideanYangMillsCompleteConstructionDirectBoundedSpectralDownstreamPackage_firstExcitationWitness S⟩

end

end MathlibAnalytic
end MGAP4D
