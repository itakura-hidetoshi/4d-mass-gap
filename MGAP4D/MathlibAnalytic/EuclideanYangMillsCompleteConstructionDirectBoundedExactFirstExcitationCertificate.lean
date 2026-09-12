import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitation
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Certificate package for the exact first excitation of the complete Yang--Mills
direct bounded construction route.

This package records the equality between the model first excitation and the
exact gap, the unique least nonzero spectral energy, exact-gap PVM support, and
the exact first-excitation sublevel classification.

It does not assert an unconditional Yang--Mills construction or a final Clay
mass-gap theorem.
-/

/-- Certificate identifying and characterizing the exact first excitation. -/
structure EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  thresholdCertificate :
    EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate S
  firstExcitationEqExactGap :
    S.definitionBridge.spine.model.firstExcitation = exactGapValueReal
  firstExcitationNonzeroSpectrum :
    S.definitionBridge.spine.model.firstExcitation ∈
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)
  firstExcitationLeast :
    IsLeast
      (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
      S.definitionBridge.spine.model.firstExcitation
  uniqueLeast :
    ∃! E : ℝ,
      IsLeast
        (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) E
  exactGapPVMWitness :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({exactGapValueReal} : Set ℝ)
  belowFirstExcitationVacuumOnly :
    S.definitionBridge.spine.model.energySpectrum ∩
        Set.Iio S.definitionBridge.spine.model.firstExcitation =
      ({0} : Set ℝ)
  firstExcitationSublevelPair :
    S.definitionBridge.spine.model.energySpectrum ∩
        Set.Iic S.definitionBridge.spine.model.firstExcitation =
      ({0, S.definitionBridge.spine.model.firstExcitation} : Set ℝ)

/-- Canonical exact-first-excitation certificate. -/
def euclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate S where
  thresholdCertificate :=
    euclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate S
  firstExcitationEqExactGap :=
    euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_eq_exactGapValueReal S
  firstExcitationNonzeroSpectrum :=
    euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_mem_nonzeroSpectrum S
  firstExcitationLeast :=
    euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_isLeast_nonzeroSpectrum S
  uniqueLeast :=
    euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_uniqueLeast S
  exactGapPVMWitness :=
    euclideanYangMillsCompleteConstructionDirectBounded_exactGapPVMWitness S
  belowFirstExcitationVacuumOnly :=
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iio_firstExcitation S
  firstExcitationSublevelPair :=
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iic_firstExcitation S

/-- Compact proposition exposed by the exact-first-excitation certificate. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitationProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    S.definitionBridge.spine.model.firstExcitation = exactGapValueReal ∧
      IsLeast
        (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
        S.definitionBridge.spine.model.firstExcitation ∧
      (∃! E : ℝ,
        IsLeast
          (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) E) ∧
      (∃ ψ : S.definitionBridge.spine.model.H,
        ψ ∈ S.definitionBridge.spine.model.spectralPVM
          ({exactGapValueReal} : Set ℝ)) ∧
      S.definitionBridge.spine.model.energySpectrum ∩
          Set.Iio S.definitionBridge.spine.model.firstExcitation =
        ({0} : Set ℝ) ∧
      S.definitionBridge.spine.model.energySpectrum ∩
          Set.Iic S.definitionBridge.spine.model.firstExcitation =
        ({0, S.definitionBridge.spine.model.firstExcitation} : Set ℝ) ∧
      euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp S

/-- Compact exact-first-excitation theorem. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitation
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitationProp S := by
  let C :=
    euclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate S
  exact ⟨
    C.firstExcitationEqExactGap,
    C.firstExcitationLeast,
    C.uniqueLeast,
    C.exactGapPVMWitness,
    C.belowFirstExcitationVacuumOnly,
    C.firstExcitationSublevelPair,
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparation S⟩

/-- Complete exact-first-excitation endpoint retaining the exact infimum formula. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitation_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitationProp S ∧
      S.definitionBridge.spine.model.firstExcitation =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitation S,
    S.definitionBridge.spine.model.firstExcitation_is_sInf_nonvacuum⟩

end

end MathlibAnalytic
end MGAP4D
