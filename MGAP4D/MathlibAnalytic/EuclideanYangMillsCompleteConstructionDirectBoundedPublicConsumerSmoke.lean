import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedPublicConsumerEndpoints
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Smoke theorems for the public consumer endpoint of the complete Yang--Mills
direct bounded route.

This file consumes the accessor and endpoint layers and exposes compact smoke
certificates for downstream users.  It deliberately uses the already certified
consumer endpoint rather than destructuring the large public package again.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Smoke proposition for the basic positive-gap consumer facts. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerBasicSmokeProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    S.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal ≠ 0

/-- Smoke theorem for the basic positive-gap consumer facts. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerBasicSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerBasicSmokeProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_hasMassGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_positiveExactGap S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_exactGap_ne_zero S⟩

/-- Smoke proposition for the exact-gap infimum surface. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerInfimumSmokeProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    0 < sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))

/-- Smoke theorem for the exact-gap infimum surface. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerInfimumSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerInfimumSmokeProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_gapInfimum_positive S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_gapFormula S⟩

/-- Smoke proposition for the witness-producing consumer facts. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWitnessSmokeProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    (∃ δ : ℝ, 0 < δ ∧
      ∀ E : ℝ,
        E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) →
        δ ≤ E ∧ 0 < E ∧ 0 ≤ E ∧ E ≠ 0) ∧
      (∃ ψ : S.definitionBridge.spine.model.H,
        ψ ∈ S.definitionBridge.spine.model.spectralPVM
          ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ))

/-- Smoke theorem for the witness-producing consumer facts. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWitnessSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWitnessSmokeProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_lowerBoundOrderWitness S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumer_firstExcitationWitness S⟩

/-- Complete smoke proposition for the public consumer endpoint. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSmokeProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerBasicSmokeProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerInfimumSmokeProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWitnessSmokeProp S

/-- Complete smoke theorem for the public consumer endpoint. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerSmokeProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerBasicSmoke S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerInfimumSmoke S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerWitnessSmoke S⟩

end

end MathlibAnalytic
end MGAP4D
