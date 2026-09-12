import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedUniqueMassGapWitness
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Certificate package for uniqueness of the mass-gap witness in the complete
Yang--Mills direct bounded construction route.

The certificate identifies the model's displayed mass-gap value, first
excitation, exact gap, and nonzero-spectrum infimum as one canonical value.  It
also upgrades the existential model-level mass-gap predicate to an equivalent
unique-witness statement.

It does not assert an unconditional Yang--Mills construction or a final Clay
mass-gap theorem.
-/

/-- The model-level mass-gap predicate is equivalent to existence of a unique
mass-gap witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_hasMassGap_iff_uniqueMassGapWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap ↔
      ∃! m : ℝ,
        euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m := by
  constructor
  · intro _hGap
    exact
      euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitness S
  · rintro ⟨m, hm, _hUnique⟩
    exact ⟨m, hm.1, hm.2.1, hm.2.2⟩

/-- The displayed mass-gap value, first excitation, exact gap, and spectral
infimum are one canonical value. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_canonicalMassGapValueChain
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.massGapValue =
        S.definitionBridge.spine.model.firstExcitation ∧
      S.definitionBridge.spine.model.firstExcitation = exactGapValueReal ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact ⟨
    S.definitionBridge.spine.model.massGapValue_eq_firstExcitation,
    euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_eq_exactGapValueReal S,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_eq_nonzeroSpectrum_sInf S⟩

/-- Certificate for the unique canonical mass-gap witness. -/
structure EuclideanYangMillsCompleteConstructionDirectBoundedUniqueMassGapWitnessCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  exactFirstExcitationCertificate :
    EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate S
  massGapValueEqExactGap :
    S.definitionBridge.spine.model.massGapValue = exactGapValueReal
  exactGapWitness :
    euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp
      S exactGapValueReal
  displayedMassGapWitness :
    euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp
      S S.definitionBridge.spine.model.massGapValue
  uniqueWitness :
    ∃! m : ℝ,
      euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m
  witnessEqExactGap :
    ∀ {m : ℝ},
      euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m →
        m = exactGapValueReal
  witnessEqFirstExcitation :
    ∀ {m : ℝ},
      euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m →
        m = S.definitionBridge.spine.model.firstExcitation
  witnessEqMassGapValue :
    ∀ {m : ℝ},
      euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m →
        m = S.definitionBridge.spine.model.massGapValue
  displayedMassGapLeast :
    IsLeast
      (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
      S.definitionBridge.spine.model.massGapValue
  displayedMassGapPVMWitness :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.massGapValue} : Set ℝ)
  belowDisplayedMassGapVacuumOnly :
    S.definitionBridge.spine.model.energySpectrum ∩
        Set.Iio S.definitionBridge.spine.model.massGapValue =
      ({0} : Set ℝ)
  displayedMassGapSublevelPair :
    S.definitionBridge.spine.model.energySpectrum ∩
        Set.Iic S.definitionBridge.spine.model.massGapValue =
      ({0, S.definitionBridge.spine.model.massGapValue} : Set ℝ)
  hasMassGapIffUniqueWitness :
    S.definitionBridge.spine.model.hasMassGap ↔
      ∃! m : ℝ,
        euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m

/-- Canonical unique-mass-gap-witness certificate. -/
def euclideanYangMillsCompleteConstructionDirectBoundedUniqueMassGapWitnessCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedUniqueMassGapWitnessCertificate S where
  exactFirstExcitationCertificate :=
    euclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate S
  massGapValueEqExactGap :=
    euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_eq_exactGapValueReal S
  exactGapWitness :=
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_massGapWitness S
  displayedMassGapWitness :=
    euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_massGapWitness S
  uniqueWitness :=
    euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitness S
  witnessEqExactGap := fun hm =>
    euclideanYangMillsCompleteConstructionDirectBounded_massGapWitness_eq_exactGap S hm
  witnessEqFirstExcitation := fun hm =>
    euclideanYangMillsCompleteConstructionDirectBounded_massGapWitness_eq_firstExcitation S hm
  witnessEqMassGapValue := fun hm =>
    euclideanYangMillsCompleteConstructionDirectBounded_massGapWitness_eq_massGapValue S hm
  displayedMassGapLeast :=
    euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_isLeast_nonzeroSpectrum S
  displayedMassGapPVMWitness :=
    euclideanYangMillsCompleteConstructionDirectBounded_massGapValuePVMWitness S
  belowDisplayedMassGapVacuumOnly :=
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iio_massGapValue S
  displayedMassGapSublevelPair :=
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iic_massGapValue S
  hasMassGapIffUniqueWitness :=
    euclideanYangMillsCompleteConstructionDirectBounded_hasMassGap_iff_uniqueMassGapWitness S

/-- Compact proposition exposed by the unique-mass-gap-witness certificate. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    S.definitionBridge.spine.model.massGapValue = exactGapValueReal ∧
      (∃! m : ℝ,
        euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m) ∧
      IsLeast
        (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
        S.definitionBridge.spine.model.massGapValue ∧
      (∃ ψ : S.definitionBridge.spine.model.H,
        ψ ∈ S.definitionBridge.spine.model.spectralPVM
          ({S.definitionBridge.spine.model.massGapValue} : Set ℝ)) ∧
      S.definitionBridge.spine.model.energySpectrum ∩
          Set.Iio S.definitionBridge.spine.model.massGapValue =
        ({0} : Set ℝ) ∧
      S.definitionBridge.spine.model.energySpectrum ∩
          Set.Iic S.definitionBridge.spine.model.massGapValue =
        ({0, S.definitionBridge.spine.model.massGapValue} : Set ℝ) ∧
      euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitationProp S

/-- Compact unique-mass-gap-witness theorem. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp S := by
  let C :=
    euclideanYangMillsCompleteConstructionDirectBoundedUniqueMassGapWitnessCertificate S
  exact ⟨
    C.massGapValueEqExactGap,
    C.uniqueWitness,
    C.displayedMassGapLeast,
    C.displayedMassGapPVMWitness,
    C.belowDisplayedMassGapVacuumOnly,
    C.displayedMassGapSublevelPair,
    euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitation S⟩

/-- Complete canonical endpoint retaining the unique-witness equivalence and the
full equality chain. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitness_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp S ∧
      (S.definitionBridge.spine.model.hasMassGap ↔
        ∃! m : ℝ,
          euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m) ∧
      (S.definitionBridge.spine.model.massGapValue =
          S.definitionBridge.spine.model.firstExcitation ∧
        S.definitionBridge.spine.model.firstExcitation = exactGapValueReal ∧
        exactGapValueReal =
          sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessCertificate S,
    euclideanYangMillsCompleteConstructionDirectBounded_hasMassGap_iff_uniqueMassGapWitness S,
    euclideanYangMillsCompleteConstructionDirectBounded_canonicalMassGapValueChain S⟩

end

end MathlibAnalytic
end MGAP4D
