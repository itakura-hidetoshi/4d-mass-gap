import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedPublicConsumerPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Public consumer accessors for the complete Yang--Mills direct bounded route.

This file consumes the public consumer package introduced by the direct bounded
route and exposes short downstream accessors for the main certified components.
It is an actual theorem-consumer layer, not a documentation-only layer.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Accessor for the mass-gap predicate from the public consumer package. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_hasMassGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap := by
  exact (euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackage S).1

/-- Accessor for positivity of the exact gap value. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_positiveExactGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    0 < exactGapValueReal := by
  exact (euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackage S).2.1

/-- Accessor for nonzeroness of the exact gap value. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_exactGap_ne_zero
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal ≠ 0 := by
  exact (euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackage S).2.2.1

/-- Accessor for positivity of the nonzero-spectrum infimum. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_gapInfimum_positive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact (euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackage S).2.2.2.1

/-- Accessor for the exact-gap formula. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_gapFormula
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact (euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackage S).2.2.2.2.1

/-- Accessor for the lower-bound order witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_lowerBoundOrderWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ E ≠ 0 := by
  exact (euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackage S).2.2.2.2.2.1

/-- Accessor for the first-excitation spectral witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_firstExcitationWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact (euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerPackage S).2.2.2.2.2.2.1

end

end MathlibAnalytic
end MGAP4D
