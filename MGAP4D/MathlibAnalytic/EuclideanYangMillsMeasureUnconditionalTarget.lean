import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline

namespace MGAP4D
namespace MathlibAnalytic

/-- Target surface for an unconditional four-dimensional Euclidean Yang--Mills
measure construction.

This is not a shortcut around the hard analytic problem.  It records the precise
non-receipt object that must be supplied before the conditional Euclidean
measure-to-mass-gap pipeline can be promoted to an unconditional theorem. -/
structure EuclideanYangMillsMeasureUnconditionalConstructionTarget where
  measurePackage : EuclideanYangMillsMeasurePackage
  bridge : EuclideanYangMillsMeasureToOSWightmanBridge
  definitionBridge : OSWightmanMassGapDefinitionBridge
  measurePackage_identified : bridge.measure = measurePackage
  bridge_uses_definition_axioms : definitionBridge.spine.axioms = bridge.axioms
  continuumFourDimensionalYangMillsMeasureConstructed : Prop
  nontrivialCompactGaugeGroupConstructed : Prop
  interactingContinuumLimitConstructed : Prop
  gaugeInvariantSchwingerFunctionsConstructed : Prop
  reflectionPositivityTheorem : measurePackage.reflectionPositive
  euclideanInvarianceTheorem : measurePackage.euclideanInvariant
  symmetryTheorem : measurePackage.symmetric
  clusterPropertyTheorem : measurePackage.clusterProperty
  regularityTheorem : measurePackage.regularity
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

/-- Readiness of the unconditional construction target.  This is a theorem-level
conjunction of the actual construction and analytic outputs. -/
def EuclideanYangMillsMeasureUnconditionalConstructionTarget.ready
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) : Prop :=
  C.continuumFourDimensionalYangMillsMeasureConstructed ∧
  C.nontrivialCompactGaugeGroupConstructed ∧
  C.interactingContinuumLimitConstructed ∧
  C.gaugeInvariantSchwingerFunctionsConstructed ∧
  C.measurePackage.ready

/-- The unconditional target supplies Euclidean measure readiness without an
external measure-side hypothesis. -/
theorem euclidean_yang_mills_unconditional_target_measure_ready
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    C.measurePackage.ready := by
  unfold EuclideanYangMillsMeasurePackage.ready
  exact ⟨
    C.gaugeGroupCompactTheorem,
    C.gaugeGroupNontrivialTheorem,
    C.reflectionPositivityTheorem,
    C.euclideanInvarianceTheorem,
    C.symmetryTheorem,
    C.clusterPropertyTheorem,
    C.regularityTheorem⟩

/-- The unconditional target is ready once its four construction-side obligations
are provided. -/
theorem euclidean_yang_mills_unconditional_target_ready
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget)
    (hMeasureConstructed : C.continuumFourDimensionalYangMillsMeasureConstructed)
    (hGaugeConstructed : C.nontrivialCompactGaugeGroupConstructed)
    (hInteractingLimit : C.interactingContinuumLimitConstructed)
    (hSchwinger : C.gaugeInvariantSchwingerFunctionsConstructed) :
    C.ready := by
  unfold EuclideanYangMillsMeasureUnconditionalConstructionTarget.ready
  exact ⟨
    hMeasureConstructed,
    hGaugeConstructed,
    hInteractingLimit,
    hSchwinger,
    euclidean_yang_mills_unconditional_target_measure_ready C⟩

/-- The target supplies readiness for the bridge's own measure carrier by
transporting along the displayed measure identification. -/
theorem euclidean_yang_mills_unconditional_target_bridge_measure_ready
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    C.bridge.measure.ready := by
  rw [C.measurePackage_identified]
  exact euclidean_yang_mills_unconditional_target_measure_ready C

/-- The unconditional construction target induces the existing Euclidean
measure-to-mass-gap pipeline without requiring an additional measure-readiness
assumption from outside the target. -/
def EuclideanYangMillsMeasureUnconditionalConstructionTarget.toPipeline
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    EuclideanYangMillsMeasureMassGapPipeline :=
  { euclideanToOSWightman := C.bridge
    definitionBridge := C.definitionBridge
    measureReady := euclidean_yang_mills_unconditional_target_bridge_measure_ready C
    bridge_uses_reconstructed_axioms := C.bridge_uses_definition_axioms }

/-- If the full unconditional construction target is supplied, the existing
Euclidean measure pipeline yields a positive normalized gap. -/
theorem euclidean_yang_mills_unconditional_target_delta_positive
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    0 < exactGapValueReal := by
  exact euclidean_yang_mills_measure_pipeline_delta_positive C.toPipeline

/-- If the full unconditional construction target is supplied, the positive gap is
the non-vacuum Hamiltonian spectral threshold. -/
theorem euclidean_yang_mills_unconditional_target_nonvacuum_threshold
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    exactGapValueReal = sInf C.toPipeline.nonVacuumHamiltonianSpectrum := by
  exact euclidean_yang_mills_measure_pipeline_nonvacuum_spectrum_threshold C.toPipeline

/-- Public theorem target for the desired unconditional route.  The only remaining
input is the construction target itself: no separate OS/Wightman readiness or
measure-readiness hypothesis appears in the theorem statement. -/
theorem euclidean_yang_mills_unconditional_measure_construction_mass_gap
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    C.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf C.toPipeline.nonVacuumHamiltonianSpectrum := by
  exact euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap
    C.toPipeline

/-- Audit-visible certificate for the target route. -/
structure EuclideanYangMillsMeasureUnconditionalConstructionCertificate
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) where
  measureReady : C.measurePackage.ready
  inducedPipeline : EuclideanYangMillsMeasureMassGapPipeline
  inducedPipeline_eq : inducedPipeline = C.toPipeline
  massGapTheorem : C.toPipeline.definitionBridge.spine.model.hasMassGap
  deltaPositive : 0 < exactGapValueReal
  nonVacuumThreshold :
    exactGapValueReal = sInf C.toPipeline.nonVacuumHamiltonianSpectrum

/-- Build the audit-visible certificate from the construction target. -/
def euclideanYangMillsMeasureUnconditionalConstructionCertificate
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    EuclideanYangMillsMeasureUnconditionalConstructionCertificate C :=
  { measureReady := euclidean_yang_mills_unconditional_target_measure_ready C
    inducedPipeline := C.toPipeline
    inducedPipeline_eq := rfl
    massGapTheorem :=
      (euclidean_yang_mills_unconditional_measure_construction_mass_gap C).1
    deltaPositive :=
      (euclidean_yang_mills_unconditional_measure_construction_mass_gap C).2.1
    nonVacuumThreshold :=
      (euclidean_yang_mills_unconditional_measure_construction_mass_gap C).2.2 }

end MathlibAnalytic
end MGAP4D
