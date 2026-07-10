import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparation
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Certificate package for exact-threshold spectral separation in the complete
Yang--Mills direct bounded construction route.

This package records the exact lower spectral classification together with the
prior interval certificate and the compact root consumer API.

It does not assert an unconditional Yang--Mills construction or a final Clay
mass-gap theorem.
-/

/-- Certificate for the exact lower spectral classification. -/
structure EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  intervalCertificate :
    EuclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate S
  nonzeroDisjointBelow :
    Disjoint
      (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
      (Set.Iio exactGapValueReal)
  belowThresholdVacuumOnly :
    S.definitionBridge.spine.model.energySpectrum ∩ Set.Iio exactGapValueReal =
      ({0} : Set ℝ)
  nonzeroSublevelSingleton :
    (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∩
        Set.Iic exactGapValueReal =
      ({exactGapValueReal} : Set ℝ)
  fullSublevelPair :
    S.definitionBridge.spine.model.energySpectrum ∩ Set.Iic exactGapValueReal =
      ({0, exactGapValueReal} : Set ℝ)
  rootConsumerAPI :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPIProp S

/-- Canonical exact-threshold separation certificate. -/
def euclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate S where
  intervalCertificate :=
    euclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate S
  nonzeroDisjointBelow :=
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_disjoint_Iio_exactGap S
  belowThresholdVacuumOnly :=
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iio_exactGap S
  nonzeroSublevelSingleton :=
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_inter_Iic_exactGap S
  fullSublevelPair :=
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iic_exactGap S
  rootConsumerAPI :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPI S

/-- Compact proposition exposed by the exact-threshold separation certificate. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    Disjoint
        (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
        (Set.Iio exactGapValueReal) ∧
      S.definitionBridge.spine.model.energySpectrum ∩ Set.Iio exactGapValueReal =
        ({0} : Set ℝ) ∧
      (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∩
          Set.Iic exactGapValueReal =
        ({exactGapValueReal} : Set ℝ) ∧
      S.definitionBridge.spine.model.energySpectrum ∩ Set.Iic exactGapValueReal =
        ({0, exactGapValueReal} : Set ℝ) ∧
      euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificateProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPIProp S

/-- Compact exact-threshold separation theorem. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparation
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp S := by
  let C :=
    euclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate S
  exact ⟨
    C.nonzeroDisjointBelow,
    C.belowThresholdVacuumOnly,
    C.nonzeroSublevelSingleton,
    C.fullSublevelPair,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificate S,
    C.rootConsumerAPI⟩

/-- Complete threshold endpoint retaining the exact infimum identity. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparation_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp S ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparation S,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_eq_nonzeroSpectrum_sInf S⟩

end

end MathlibAnalytic
end MGAP4D
