import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
import MGAP4D.MathlibAnalytic.OSWightmanExactGapReducedReconstruction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
A dependency-reduced continuum Yang--Mills construction spine.

The existing continuum construction spine asks for a full mass-gap definition
bridge and repeats several theorem fields already available from that bridge.
This reduced spine instead carries `OSWightmanExactGapDefinitionBridge` and
constructs the existing spine canonically.

Positive energy, vacuum isolation, first excitation, the displayed mass-gap
value, Hamiltonian self-adjointness, PVM detection, and the vacuum spectral point
are not repeated as independent top-level inputs.
-/

/-- Continuum finite-volume/limit construction data using the reduced exact-gap
OS/Wightman bridge. -/
structure EuclideanYangMillsContinuumMeasureExactGapConstructionSpine where
  finiteVolume : EuclideanYangMillsFiniteVolumeApproximation
  measurePackage : EuclideanYangMillsMeasurePackage
  bridge : EuclideanYangMillsMeasureToOSWightmanBridge
  definitionBridge : OSWightmanExactGapDefinitionBridge
  measurePackage_identified : bridge.measure = measurePackage
  bridge_uses_reduced_axioms : definitionBridge.spine.axioms = bridge.axioms
  projectiveConsistency : Prop
  projectiveConsistency_proof : projectiveConsistency
  tightness : Prop
  tightness_proof : tightness
  weakLimitExists : Prop
  weakLimitExists_proof : weakLimitExists
  continuumMeasureIdentified : Prop
  continuumMeasureIdentified_proof : continuumMeasureIdentified
  continuumFourDimensionalYangMillsMeasureConstructed : Prop
  continuumFourDimensionalYangMillsMeasureConstructed_proof :
    continuumFourDimensionalYangMillsMeasureConstructed
  nontrivialCompactGaugeGroupConstructed : Prop
  nontrivialCompactGaugeGroupConstructed_proof :
    nontrivialCompactGaugeGroupConstructed
  interactingContinuumLimitConstructed : Prop
  interactingContinuumLimitConstructed_proof :
    interactingContinuumLimitConstructed
  gaugeInvariantSchwingerFunctionsConstructed : Prop
  gaugeInvariantSchwingerFunctionsConstructed_proof :
    gaugeInvariantSchwingerFunctionsConstructed
  schwingerFunctionsAreContinuumLimits : Prop
  schwingerFunctionsAreContinuumLimits_proof :
    schwingerFunctionsAreContinuumLimits
  reflectionPositivityPassesToLimit : measurePackage.reflectionPositive
  euclideanInvariancePassesToLimit : measurePackage.euclideanInvariant
  symmetryPassesToLimit : measurePackage.symmetric
  clusterPropertyPassesToLimit : measurePackage.clusterProperty
  regularityPassesToLimit : measurePackage.regularity
  gaugeGroupCompactTheorem : measurePackage.gaugeGroupCompact
  gaugeGroupNontrivialTheorem : measurePackage.gaugeGroupNontrivial

/-- The reduced continuum spine has the same finite-volume/continuum limit
readiness predicate as the existing spine. -/
def EuclideanYangMillsContinuumMeasureExactGapConstructionSpine.limitReady
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) : Prop :=
  S.finiteVolume.gaugeInvariantFiniteVolume ∧
    S.finiteVolume.finiteVolumeReflectionPositive ∧
    S.finiteVolume.finiteVolumeEuclideanCovariant ∧
    S.projectiveConsistency ∧
    S.tightness ∧
    S.weakLimitExists ∧
    S.continuumMeasureIdentified ∧
    S.schwingerFunctionsAreContinuumLimits

/-- Limit readiness follows directly from the theorem-bearing reduced spine. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_limitReady
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.limitReady := by
  exact ⟨
    S.finiteVolume.gaugeInvariantFiniteVolume_proof,
    S.finiteVolume.finiteVolumeReflectionPositive_proof,
    S.finiteVolume.finiteVolumeEuclideanCovariant_proof,
    S.projectiveConsistency_proof,
    S.tightness_proof,
    S.weakLimitExists_proof,
    S.continuumMeasureIdentified_proof,
    S.schwingerFunctionsAreContinuumLimits_proof⟩

/-- Convert the reduced exact-gap continuum spine to the existing full
construction spine.

All Hamiltonian/PVM/spectral theorem fields are generated from the reduced
bridge. -/
def EuclideanYangMillsContinuumMeasureExactGapConstructionSpine.toConstructionSpine
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    EuclideanYangMillsContinuumMeasureConstructionSpine where
  finiteVolume := S.finiteVolume
  measurePackage := S.measurePackage
  bridge := S.bridge
  definitionBridge := S.definitionBridge.toDefinitionBridge
  measurePackage_identified := S.measurePackage_identified
  bridge_uses_definition_axioms := by
    change S.definitionBridge.spine.axioms = S.bridge.axioms
    exact S.bridge_uses_reduced_axioms
  projectiveConsistency := S.projectiveConsistency
  projectiveConsistency_proof := S.projectiveConsistency_proof
  tightness := S.tightness
  tightness_proof := S.tightness_proof
  weakLimitExists := S.weakLimitExists
  weakLimitExists_proof := S.weakLimitExists_proof
  continuumMeasureIdentified := S.continuumMeasureIdentified
  continuumMeasureIdentified_proof := S.continuumMeasureIdentified_proof
  continuumFourDimensionalYangMillsMeasureConstructed :=
    S.continuumFourDimensionalYangMillsMeasureConstructed
  continuumFourDimensionalYangMillsMeasureConstructed_proof :=
    S.continuumFourDimensionalYangMillsMeasureConstructed_proof
  nontrivialCompactGaugeGroupConstructed :=
    S.nontrivialCompactGaugeGroupConstructed
  nontrivialCompactGaugeGroupConstructed_proof :=
    S.nontrivialCompactGaugeGroupConstructed_proof
  interactingContinuumLimitConstructed :=
    S.interactingContinuumLimitConstructed
  interactingContinuumLimitConstructed_proof :=
    S.interactingContinuumLimitConstructed_proof
  gaugeInvariantSchwingerFunctionsConstructed :=
    S.gaugeInvariantSchwingerFunctionsConstructed
  gaugeInvariantSchwingerFunctionsConstructed_proof :=
    S.gaugeInvariantSchwingerFunctionsConstructed_proof
  schwingerFunctionsAreContinuumLimits :=
    S.schwingerFunctionsAreContinuumLimits
  schwingerFunctionsAreContinuumLimits_proof :=
    S.schwingerFunctionsAreContinuumLimits_proof
  reflectionPositivityPassesToLimit := S.reflectionPositivityPassesToLimit
  euclideanInvariancePassesToLimit := S.euclideanInvariancePassesToLimit
  symmetryPassesToLimit := S.symmetryPassesToLimit
  clusterPropertyPassesToLimit := S.clusterPropertyPassesToLimit
  regularityPassesToLimit := S.regularityPassesToLimit
  gaugeGroupCompactTheorem := S.gaugeGroupCompactTheorem
  gaugeGroupNontrivialTheorem := S.gaugeGroupNontrivialTheorem
  hamiltonianSelfAdjointTheorem :=
    S.definitionBridge.hamiltonianSelfAdjoint_proof
  spectralPVMDetectionTheorem :=
    S.definitionBridge.spectralPVM_detects_energySpectrum
  vacuumSpectralPointTheorem :=
    S.definitionBridge.vacuumSpectralPoint
  positiveEnergyTheorem := fun _hSpectrum =>
    S.definitionBridge.positiveEnergy
  vacuumIsolationTheorem := fun _hCluster =>
    S.definitionBridge.spine.spectralCore.vacuumIsolated

/-- The conversion preserves the Euclidean measure package. -/
theorem EuclideanYangMillsContinuumMeasureExactGapConstructionSpine.toConstructionSpine_measurePackage
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.measurePackage = S.measurePackage := by
  rfl

/-- The conversion uses the full bridge generated from the reduced bridge. -/
theorem EuclideanYangMillsContinuumMeasureExactGapConstructionSpine.toConstructionSpine_definitionBridge
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.definitionBridge =
      S.definitionBridge.toDefinitionBridge := by
  rfl

/-- The converted model is the canonical model generated by the reduced spectral
core. -/
theorem EuclideanYangMillsContinuumMeasureExactGapConstructionSpine.toConstructionSpine_model
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.definitionBridge.spine.model =
      S.definitionBridge.spine.spectralCore.toAxiomaticModel := by
  rfl

/-- The converted construction spine has the same exact-gap energy spectrum as
the reduced spectral core. -/
theorem EuclideanYangMillsContinuumMeasureExactGapConstructionSpine.toConstructionSpine_energySpectrum
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.definitionBridge.spine.model.energySpectrum =
      S.definitionBridge.spine.spectralCore.energySpectrum := by
  rfl

/-- The converted first excitation is definitionally the exact gap. -/
theorem EuclideanYangMillsContinuumMeasureExactGapConstructionSpine.toConstructionSpine_firstExcitation
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.definitionBridge.spine.model.firstExcitation =
      exactGapValueReal := by
  rfl

/-- The converted displayed mass-gap value is definitionally the exact gap. -/
theorem EuclideanYangMillsContinuumMeasureExactGapConstructionSpine.toConstructionSpine_massGapValue
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.definitionBridge.spine.model.massGapValue =
      exactGapValueReal := by
  rfl

end

end MathlibAnalytic
end MGAP4D
