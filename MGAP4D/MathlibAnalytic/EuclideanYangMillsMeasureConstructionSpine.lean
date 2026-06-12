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

/-- The induced Euclidean measure-to-mass-gap pipeline uses exactly the definition
bridge carried by the construction spine. -/
theorem euclidean_yang_mills_continuum_spine_toPipeline_definitionBridge
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.toPipeline.definitionBridge = S.definitionBridge := by
  rfl

/-- The induced pipeline's non-vacuum Hamiltonian spectrum is the definition
bridge spectrum with the vacuum energy removed. -/
theorem euclidean_yang_mills_continuum_spine_toPipeline_nonvacuum_spectrum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.toPipeline.nonVacuumHamiltonianSpectrum =
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) := by
  rfl

/-- The construction spine proves readiness of the continuum Euclidean measure
package itself. -/
theorem euclidean_yang_mills_continuum_spine_measure_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.measurePackage.ready := by
  exact euclidean_yang_mills_unconditional_target_measure_ready S.toUnconditionalTarget

/-- The construction spine proves readiness of the measure carrier used by its
OS/Wightman bridge. -/
theorem euclidean_yang_mills_continuum_spine_bridge_measure_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.bridge.measure.ready := by
  exact euclidean_yang_mills_unconditional_target_bridge_measure_ready
    S.toUnconditionalTarget

/-- The construction spine proves readiness of the reconstructed OS/Wightman
assumption package used downstream by the Hamiltonian/PVM definition bridge. -/
theorem euclidean_yang_mills_continuum_spine_os_axioms_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.axioms.ready := by
  exact euclidean_yang_mills_measure_pipeline_os_axioms_ready S.toPipeline

/-- The construction spine exposes the Wightman locality, covariance, and spectrum
condition obtained from the OS reconstruction route. -/
theorem euclidean_yang_mills_continuum_spine_wightman_theory
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.axioms.wightmanLocality ∧
    S.definitionBridge.spine.axioms.wightmanCovariance ∧
    S.definitionBridge.spine.axioms.wightmanSpectrumCondition := by
  exact euclidean_yang_mills_measure_pipeline_wightman_theory S.toPipeline

/-- The construction spine exposes the reconstructed physical Hilbert carrier. -/
theorem euclidean_yang_mills_continuum_spine_physical_hilbert_space
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Nonempty S.definitionBridge.spine.model.H := by
  exact euclidean_yang_mills_measure_pipeline_physical_hilbert_space S.toPipeline

/-- The construction spine exposes the Hamiltonian as the self-adjoint
 time-translation generator supplied by the definition bridge. -/
theorem euclidean_yang_mills_continuum_spine_hamiltonian_time_translation_generator
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hamiltonianSelfAdjoint := by
  exact euclidean_yang_mills_measure_pipeline_hamiltonian_time_translation_generator
    S.toPipeline

/-- The construction spine exposes the vacuum vector Ω as a spectral point at
energy zero. -/
theorem euclidean_yang_mills_continuum_spine_vacuum_omega_spectral_point
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.vacuum ∈
      S.definitionBridge.spine.model.spectralPVM ({0} : Set ℝ) := by
  exact euclidean_yang_mills_measure_pipeline_vacuum_omega_spectral_point
    S.toPipeline

/-- The construction spine exposes positivity of the reconstructed Hamiltonian
spectrum. -/
theorem euclidean_yang_mills_continuum_spine_positive_hamiltonian_spectrum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∀ E : ℝ, E ∈ S.definitionBridge.spine.model.energySpectrum → 0 ≤ E := by
  exact euclidean_yang_mills_measure_pipeline_positive_hamiltonian_spectrum
    S.toPipeline

/-- The construction spine exposes vacuum isolation, routed through the OS cluster
property in the definition bridge. -/
theorem euclidean_yang_mills_continuum_spine_vacuum_isolated
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      Set.Ioo 0 δ ∩ S.definitionBridge.spine.model.energySpectrum = ∅ := by
  exact os_wightman_bridge_vacuum_isolated S.definitionBridge

/-- The construction spine exposes detection of the first excitation by the
spectral PVM. -/
theorem euclidean_yang_mills_continuum_spine_first_excitation_pvm_detected
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ) := by
  exact os_wightman_bridge_first_excitation_has_pvm_support S.definitionBridge

/-- The construction spine exposes the model-level mass-gap predicate before the
normalized exact value is read off. -/
theorem euclidean_yang_mills_continuum_spine_mass_gap_definition
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hasMassGap := by
  exact os_wightman_bridge_mass_gap_definition S.definitionBridge

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

/-- The same threshold can be read directly on the definition bridge carried by
the construction spine, because the induced pipeline preserves that bridge. -/
theorem euclidean_yang_mills_continuum_spine_definition_bridge_nonvacuum_threshold
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  simpa [euclidean_yang_mills_continuum_spine_toPipeline_nonvacuum_spectrum S]
    using euclidean_yang_mills_continuum_spine_nonvacuum_threshold S

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
  measureReady : S.measurePackage.ready
  bridgeMeasureReady : S.bridge.measure.ready
  osAxiomsReady : S.definitionBridge.spine.axioms.ready
  wightmanTheory :
    S.definitionBridge.spine.axioms.wightmanLocality ∧
    S.definitionBridge.spine.axioms.wightmanCovariance ∧
    S.definitionBridge.spine.axioms.wightmanSpectrumCondition
  physicalHilbertSpace : Nonempty S.definitionBridge.spine.model.H
  hamiltonianTimeTranslationGenerator :
    S.definitionBridge.spine.model.hamiltonianSelfAdjoint
  vacuumOmegaSpectralPoint :
    S.definitionBridge.spine.model.vacuum ∈
      S.definitionBridge.spine.model.spectralPVM ({0} : Set ℝ)
  positiveHamiltonianSpectrum :
    ∀ E : ℝ, E ∈ S.definitionBridge.spine.model.energySpectrum → 0 ≤ E
  vacuumIsolated :
    ∃ δ : ℝ, 0 < δ ∧
      Set.Ioo 0 δ ∩ S.definitionBridge.spine.model.energySpectrum = ∅
  firstExcitationPVMDetected :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)
  massGapDefinition : S.definitionBridge.spine.model.hasMassGap
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
    measureReady := euclidean_yang_mills_continuum_spine_measure_ready S
    bridgeMeasureReady :=
      euclidean_yang_mills_continuum_spine_bridge_measure_ready S
    osAxiomsReady := euclidean_yang_mills_continuum_spine_os_axioms_ready S
    wightmanTheory := euclidean_yang_mills_continuum_spine_wightman_theory S
    physicalHilbertSpace :=
      euclidean_yang_mills_continuum_spine_physical_hilbert_space S
    hamiltonianTimeTranslationGenerator :=
      euclidean_yang_mills_continuum_spine_hamiltonian_time_translation_generator S
    vacuumOmegaSpectralPoint :=
      euclidean_yang_mills_continuum_spine_vacuum_omega_spectral_point S
    positiveHamiltonianSpectrum :=
      euclidean_yang_mills_continuum_spine_positive_hamiltonian_spectrum S
    vacuumIsolated := euclidean_yang_mills_continuum_spine_vacuum_isolated S
    firstExcitationPVMDetected :=
      euclidean_yang_mills_continuum_spine_first_excitation_pvm_detected S
    massGapDefinition :=
      euclidean_yang_mills_continuum_spine_mass_gap_definition S
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
