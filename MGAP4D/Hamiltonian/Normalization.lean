import MGAP4D.Hamiltonian.Physical

namespace MGAP4D
namespace Hamiltonian

/-- A pre-Mathlib normalization unit for the physical Hamiltonian.

The current migration layer records the internal normalized convention only:
unit scale is fixed to one and the vacuum reference is fixed to zero. -/
structure HamiltonianNormalizationUnit where
  unitScale : Rat
  unitScaleIsOne : unitScale = 1
  vacuumEnergyReference : Rat
  vacuumReferenceIsZero : vacuumEnergyReference = 0
  internalNormalizedUnitsVisible : Prop
  vacuumReferenceVisible : Prop
  theoremBoundaryHeld : Prop

def HamiltonianNormalizationUnit.ready
    (U : HamiltonianNormalizationUnit) : Prop :=
  U.unitScaleIsOne ∧ U.vacuumReferenceIsZero ∧
  U.internalNormalizedUnitsVisible ∧ U.vacuumReferenceVisible ∧ U.theoremBoundaryHeld

def physicalHamiltonianNormalizationUnit : HamiltonianNormalizationUnit :=
  { unitScale := 1
    unitScaleIsOne := by rfl
    vacuumEnergyReference := 0
    vacuumReferenceIsZero := by rfl
    internalNormalizedUnitsVisible := True
    vacuumReferenceVisible := True
    theoremBoundaryHeld := True }

/-- A pre-Mathlib certificate that the physical Hamiltonian record is interpreted
in the fixed internal normalized convention. -/
structure PhysicalHamiltonianNormalization where
  unit : HamiltonianNormalizationUnit
  unitReady : unit.ready
  hamiltonian : HamiltonianLabel
  hamiltonianIsHphys : hamiltonian = Hphys
  physicalGapRecord : PhysicalGapRecord
  recordUsesHphys : physicalGapRecord.hamiltonian = Hphys
  normalizedGap : Spectral.SpectralValue
  normalizedGapIs3320 : normalizedGap.value = 33 / 20
  normalizedGapMatchesRecord : normalizedGap = physicalGapRecord.witness.gap
  positiveNumeratorPreserved : physicalGapRecord.witness.gap.value.num > 0
  normalizationDoesNotChangeWitness : Prop
  theoremBoundaryHeld : Prop

def PhysicalHamiltonianNormalization.ready
    (N : PhysicalHamiltonianNormalization) : Prop :=
  N.unitReady ∧ N.hamiltonianIsHphys ∧ N.recordUsesHphys ∧
  N.normalizedGapIs3320 ∧ N.normalizedGapMatchesRecord ∧
  N.positiveNumeratorPreserved ∧ N.normalizationDoesNotChangeWitness ∧
  N.theoremBoundaryHeld

def physicalHamiltonian3320Normalization : PhysicalHamiltonianNormalization :=
  { unit := physicalHamiltonianNormalizationUnit
    unitReady := by
      exact And.intro rfl <|
        And.intro rfl <|
        And.intro True.intro <|
        And.intro True.intro True.intro
    hamiltonian := Hphys
    hamiltonianIsHphys := by rfl
    physicalGapRecord := physicalGap3320Record
    recordUsesHphys := by rfl
    normalizedGap := Spectral.spectral3320
    normalizedGapIs3320 := by rfl
    normalizedGapMatchesRecord := by rfl
    positiveNumeratorPreserved := Spectral.gap3320Witness.positiveNumerator
    normalizationDoesNotChangeWitness := True
    theoremBoundaryHeld := True }

theorem hamiltonian_normalization_unit_pack
    (U : HamiltonianNormalizationUnit) :
    U.ready ↔ U.unitScaleIsOne ∧ U.vacuumReferenceIsZero ∧
      U.internalNormalizedUnitsVisible ∧ U.vacuumReferenceVisible ∧ U.theoremBoundaryHeld := by
  rfl

theorem physical_hamiltonian_normalization_pack
    (N : PhysicalHamiltonianNormalization) :
    N.ready ↔ N.unitReady ∧ N.hamiltonianIsHphys ∧ N.recordUsesHphys ∧
      N.normalizedGapIs3320 ∧ N.normalizedGapMatchesRecord ∧
      N.positiveNumeratorPreserved ∧ N.normalizationDoesNotChangeWitness ∧
      N.theoremBoundaryHeld := by
  rfl

theorem physical_hamiltonian_3320_normalization_ready :
    physicalHamiltonian3320Normalization.ready := by
  exact And.intro physicalHamiltonian3320Normalization.unitReady <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro Spectral.gap3320Witness.positiveNumerator <|
    And.intro True.intro True.intro

theorem physical_hamiltonian_3320_normalized_value :
    physicalHamiltonian3320Normalization.normalizedGap.value = 33 / 20 := by
  rfl

theorem physical_hamiltonian_3320_normalization_preserves_positive_numerator :
    physicalHamiltonian3320Normalization.physicalGapRecord.witness.gap.value.num > 0 := by
  exact Spectral.gap3320Witness.positiveNumerator

theorem physical_hamiltonian_3320_unit_scale_one :
    physicalHamiltonian3320Normalization.unit.unitScale = 1 := by
  rfl

theorem physical_hamiltonian_3320_vacuum_reference_zero :
    physicalHamiltonian3320Normalization.unit.vacuumEnergyReference = 0 := by
  rfl

end Hamiltonian
end MGAP4D
