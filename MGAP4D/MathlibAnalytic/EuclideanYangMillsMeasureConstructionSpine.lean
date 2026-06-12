import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget

namespace MGAP4D
namespace MathlibAnalytic

/-- Finite-volume Euclidean Yang--Mills approximation data.

This is the first upstream construction spine above the unconditional target.  It
keeps the finite-volume measures as genuine Mathlib measure carriers, while the
hard analytic properties are theorem fields that a concrete construction must
supply. -/
structure EuclideanYangMillsFiniteVolumeApproximation where
  index : Type
  finiteVolumeConfiguration : index → Type
  finiteVolumeMeasurableSpace :
    (i : index) → MeasurableSpace (finiteVolumeConfiguration i)
  finiteVolumeMeasure :
    (i : index) → @MeasureTheory.Measure
      (finiteVolumeConfiguration i) (finiteVolumeMeasurableSpace i)
  latticeSpacing : index → ℝ
  volumeScale : index → ℝ
  gaugeInvariantFiniteVolume : Prop
  gaugeInvariantFiniteVolume_proof : gaugeInvariantFiniteVolume
  finiteVolumeReflectionPositive : Prop
  finiteVolumeReflectionPositive_proof : finiteVolumeReflectionPositive
  finiteVolumeEuclideanCovariant : Prop
  finiteVolumeEuclideanCovariant_proof : finiteVolumeEuclideanCovariant
  finiteVolumeSchwingerData : ℕ → Type

/-- Continuum-limit construction data for the Euclidean Yang--Mills measure.

The fields are deliberately theorem-bearing: tightness, projective consistency,
weak-limit existence, OS positivity in the limit, and Schwinger-function
convergence are all visible obligations. -/
structure EuclideanYangMillsContinuumMeasureConstructionSpine where
  finiteVolume : EuclideanYangMillsFiniteVolumeApproximation
  measurePackage : EuclideanYangMillsMeasurePackage
  bridge : EuclideanYangMillsMeasureToOSWightmanBridge
  definitionBridge : OSWightmanMassGapDefinitionBridge
  measurePackage_identified : bridge.measure = measurePackage
  bridge_uses_definition_axioms : definitionBridge.spine.axioms = bridge.axioms
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
  nontrivialCompactGaugeGroupConstructed_proof : nontrivialCompactGaugeGroupConstructed
  interactingContinuumLimitConstructed : Prop
  interactingContinuumLimitConstructed_proof : interactingContinuumLimitConstructed
  gaugeInvariantSchwingerFunctionsConstructed : Prop
  gaugeInvariantSchwingerFunctionsConstructed_proof :
    gaugeInvariantSchwingerFunctionsConstructed
  schwingerFunctionsAreContinuumLimits : Prop
  schwingerFunctionsAreContinuumLimits_proof : schwingerFunctionsAreContinuumLimits
  reflectionPositivityPassesToLimit : measurePackage.reflectionPositive
  euclideanInvariancePassesToLimit : measurePackage.euclideanInvariant
  symmetryPassesToLimit : measurePackage.symmetric
  clusterPropertyPassesToLimit : measurePackage.clusterProperty
  regularityPassesToLimit : measurePackage.regularity
  gaugeGroupCompactTheorem : measurePackage.gaugeGroupCompact
  gaugeGroupNontrivialTheorem : measurePackage.gaugeGroupNontrivial
  hamiltonianSelfAdjointTheorem : definitionBridge.spine.model.hamiltonianSelfAdjoint
  spectralPVMDetectionTheorem :
    ∀ E : ℝ, E ∈ definitionBridge.spine.model.energySpectrum →
      ∃ ψ : definitionBridge.spine.model.H,
        ψ ∈ definitionBridge.spine.model.spectralPVM ({E} : Set ℝ)
  vacuumSpectralPointTheorem :
    definitionBridge.spine.model.vacuum ∈
      definitionBridge.spine.model.spectralPVM ({0} : Set ℝ)
  positiveEnergyTheorem :
    definitionBridge.spine.axioms.wightmanSpectrumCondition →
      ∀ E : ℝ, E ∈ definitionBridge.spine.model.energySpectrum → 0 ≤ E
  vacuumIsolationTheorem :
    definitionBridge.spine.axioms.osClusterProperty →
      ∃ δ : ℝ, 0 < δ ∧
        Set.Ioo 0 δ ∩ definitionBridge.spine.model.energySpectrum = ∅

/-- The continuum construction spine records the analytic compactness and limit
existence route needed to construct the Euclidean measure. -/
def EuclideanYangMillsContinuumMeasureConstructionSpine.limitReady
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
  S.finiteVolume.gaugeInvariantFiniteVolume ∧
  S.finiteVolume.finiteVolumeReflectionPositive ∧
  S.finiteVolume.finiteVolumeEuclideanCovariant ∧
  S.projectiveConsistency ∧
  S.tightness ∧
  S.weakLimitExists ∧
  S.continuumMeasureIdentified ∧
  S.schwingerFunctionsAreContinuumLimits

/-- The finite-volume/continuum spine proves limit readiness without taking any
extra theorem parameter outside the spine. -/
theorem euclidean_yang_mills_continuum_spine_limit_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.limitReady := by
  unfold EuclideanYangMillsContinuumMeasureConstructionSpine.limitReady
  exact ⟨
    S.finiteVolume.gaugeInvariantFiniteVolume_proof,
    S.finiteVolume.finiteVolumeReflectionPositive_proof,
    S.finiteVolume.finiteVolumeEuclideanCovariant_proof,
    S.projectiveConsistency_proof,
    S.tightness_proof,
    S.weakLimitExists_proof,
    S.continuumMeasureIdentified_proof,
    S.schwingerFunctionsAreContinuumLimits_proof⟩

/-- Convert the finite-volume/continuum construction spine into the unconditional
Euclidean-measure construction target. -/
def EuclideanYangMillsContinuumMeasureConstructionSpine.toUnconditionalTarget
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsMeasureUnconditionalConstructionTarget :=
  { measurePackage := S.measurePackage
    bridge := S.bridge
    definitionBridge := S.definitionBridge
    measurePackage_identified := S.measurePackage_identified
    bridge_uses_definition_axioms := S.bridge_uses_definition_axioms
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
    reflectionPositivityTheorem := S.reflectionPositivityPassesToLimit
    euclideanInvarianceTheorem := S.euclideanInvariancePassesToLimit
    symmetryTheorem := S.symmetryPassesToLimit
    clusterPropertyTheorem := S.clusterPropertyPassesToLimit
    regularityTheorem := S.regularityPassesToLimit
    gaugeGroupCompactTheorem := S.gaugeGroupCompactTheorem
    gaugeGroupNontrivialTheorem := S.gaugeGroupNontrivialTheorem
    hamiltonianSelfAdjointTheorem := S.hamiltonianSelfAdjointTheorem
    spectralPVMDetectionTheorem := S.spectralPVMDetectionTheorem
    vacuumSpectralPointTheorem := S.vacuumSpectralPointTheorem
    positiveEnergyTheorem := S.positiveEnergyTheorem
    vacuumIsolationTheorem := S.vacuumIsolationTheorem }

/-- The construction spine proves that the induced unconditional target is ready. -/
theorem euclidean_yang_mills_continuum_spine_unconditional_target_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.toUnconditionalTarget.ready := by
  exact euclidean_yang_mills_unconditional_target_ready S.toUnconditionalTarget

/-- The finite-volume/continuum construction spine induces the full Euclidean
measure-to-mass-gap pipeline. -/
def EuclideanYangMillsContinuumMeasureConstructionSpine.toPipeline
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsMeasureMassGapPipeline :=
  S.toUnconditionalTarget.toPipeline

/-- Main construction-spine theorem: once the finite-volume approximation,
continuum limit, OS positivity, Schwinger-function construction, and
Hamiltonian/PVM bridge fields are supplied, the normalized gap is positive. -/
theorem euclidean_yang_mills_continuum_spine_delta_positive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    0 < exactGapValueReal := by
  exact euclidean_yang_mills_unconditional_target_delta_positive
    S.toUnconditionalTarget

/-- The same construction spine identifies the positive gap with the non-vacuum
Hamiltonian spectral threshold. -/
theorem euclidean_yang_mills_continuum_spine_nonvacuum_threshold
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum := by
  exact euclidean_yang_mills_unconditional_target_nonvacuum_threshold
    S.toUnconditionalTarget

/-- End-to-end theorem from the finite-volume/continuum construction spine to the
mass-gap statement. -/
theorem euclidean_yang_mills_finite_volume_continuum_construction_mass_gap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum := by
  exact euclidean_yang_mills_unconditional_measure_construction_mass_gap
    S.toUnconditionalTarget

/-- Audit-visible certificate for the finite-volume/continuum construction spine. -/
structure EuclideanYangMillsContinuumMeasureConstructionCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  limitReady : S.limitReady
  unconditionalTargetReady : S.toUnconditionalTarget.ready
  inducedPipeline : EuclideanYangMillsMeasureMassGapPipeline
  inducedPipeline_eq : inducedPipeline = S.toPipeline
  massGapTheorem : S.toPipeline.definitionBridge.spine.model.hasMassGap
  deltaPositive : 0 < exactGapValueReal
  nonVacuumThreshold :
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum

/-- Build the finite-volume/continuum construction certificate. -/
def euclideanYangMillsContinuumMeasureConstructionCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsContinuumMeasureConstructionCertificate S :=
  { limitReady := euclidean_yang_mills_continuum_spine_limit_ready S
    unconditionalTargetReady :=
      euclidean_yang_mills_continuum_spine_unconditional_target_ready S
    inducedPipeline := S.toPipeline
    inducedPipeline_eq := rfl
    massGapTheorem :=
      (euclidean_yang_mills_finite_volume_continuum_construction_mass_gap S).1
    deltaPositive :=
      (euclidean_yang_mills_finite_volume_continuum_construction_mass_gap S).2.1
    nonVacuumThreshold :=
      (euclidean_yang_mills_finite_volume_continuum_construction_mass_gap S).2.2 }

end MathlibAnalytic
end MGAP4D
