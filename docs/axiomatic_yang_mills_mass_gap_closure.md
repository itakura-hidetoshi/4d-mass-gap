# Axiomatic Yang--Mills Mass Gap Closure Route

This note records the conditional proof kernel installed in
`MGAP4D/MathlibAnalytic/AxiomaticYangMillsMassGapClosure.lean`, its external
audit projection in
`MGAP4D/MathlibAnalytic/AxiomaticYangMillsExternalAuditProjection.lean`, the
OS/Wightman-to-Hamiltonian reconstruction spine in
`MGAP4D/MathlibAnalytic/OSWightmanHamiltonianReconstructionSpine.lean`, the
OS/Wightman mass-gap definition bridge in
`MGAP4D/MathlibAnalytic/OSWightmanMassGapDefinitionBridge.lean`, its external
audit projection in
`MGAP4D/MathlibAnalytic/OSWightmanMassGapExternalAuditBridge.lean`, the
Euclidean-measure-to-mass-gap pipeline in
`MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureToMassGapPipeline.lean`, the
unconditional-construction target in
`MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureUnconditionalTarget.lean`, the
finite-volume/continuum construction spine in
`MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionSpine.lean`, and
the construction-spine external audit bridge in
`MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean`.

## Scope

The repository surface does **not** claim an unconditional solution of the Clay
Yang--Mills mass gap problem.  It records theorem-level closure targets and
reviewable bridge surfaces over displayed Mathlib data:

- Euclidean Yang--Mills measure data,
- finite-volume Mathlib measure carriers,
- tightness / weak-limit / projective-consistency construction fields,
- Osterwalder--Schrader assumption package,
- Wightman assumption package,
- reconstructed Hilbert-space carrier,
- Hamiltonian,
- vacuum,
- spectral PVM interface,
- positive-energy condition,
- isolated vacuum,
- positive first non-vacuum spectral excitation.

## Closure theorem

```lean
theorem wightman_os_hamiltonian_spectral_pvm_closes_4d_mass_gap
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready) :
    M.hasMassGap ∧ 0 < M.massGapValue ∧
      M.massGapValue = sInf (M.energySpectrum \ ({0} : Set ℝ))
```

## External audit projection

```lean
theorem external_audit_readiness_axiomatic_yang_mills_closure_projection
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready) :
    ExternalAuditReadinessAxiomaticYangMillsClosureProjection M

theorem external_audit_readiness_axiomatic_yang_mills_exact_gap_projection
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready)
    (hExact : M.massGapValue = exactGapValueReal) :
    ExternalAuditReadinessAxiomaticYangMillsExactGapProjection M
```

## Reconstruction spine

```lean
structure OSWightmanHamiltonianReconstructionSpine where
  axioms : OSWightmanYangMillsAxioms
  model : FourDimensionalYangMillsAxiomaticModel
  model_uses_axioms : model.osWightman = axioms
  axioms_ready : axioms.ready
  exact_gap_value_identified : model.massGapValue = exactGapValueReal

theorem os_wightman_reconstruction_spine_has_mass_gap
    (S : OSWightmanHamiltonianReconstructionSpine) :
    S.model.hasMassGap

theorem os_wightman_reconstruction_spine_exact_gap_positive
    (S : OSWightmanHamiltonianReconstructionSpine) :
    0 < exactGapValueReal

theorem os_wightman_reconstruction_spine_exact_gap_is_sInf_nonvacuum
    (S : OSWightmanHamiltonianReconstructionSpine) :
    exactGapValueReal = sInf (S.model.energySpectrum \ ({0} : Set ℝ))
```

## Definition bridge

```lean
structure OSWightmanMassGapDefinitionBridge where
  spine : OSWightmanHamiltonianReconstructionSpine
  hamiltonianSelfAdjoint_proof : spine.model.hamiltonianSelfAdjoint
  spectralPVM_detects_energySpectrum :
    ∀ E : ℝ, E ∈ spine.model.energySpectrum →
      ∃ ψ : spine.model.H, ψ ∈ spine.model.spectralPVM ({E} : Set ℝ)
  vacuumSpectralPoint :
    spine.model.vacuum ∈ spine.model.spectralPVM ({0} : Set ℝ)
  positiveEnergy_from_wightmanSpectrum :
    spine.axioms.wightmanSpectrumCondition →
      ∀ E : ℝ, E ∈ spine.model.energySpectrum → 0 ≤ E
  vacuumIsolation_from_osCluster :
    spine.axioms.osClusterProperty →
      ∃ δ : ℝ, 0 < δ ∧ Set.Ioo 0 δ ∩ spine.model.energySpectrum = ∅
```

The certificate `OSWightmanMassGapDefinitionBridgeCertificate` records positive
energy, vacuum isolation, PVM detection, the model-level mass-gap predicate, and
the exact spectral-threshold identity as theorem fields.

## OS/Wightman external bridge audit surface

```lean
theorem external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection
    (B : OSWightmanMassGapDefinitionBridge) :
    ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection B

theorem external_audit_readiness_os_wightman_definition_bridge_exact_gap_positive
    (B : OSWightmanMassGapDefinitionBridge) :
    0 < exactGapValueReal

theorem external_audit_readiness_os_wightman_definition_bridge_exact_gap_threshold
    (B : OSWightmanMassGapDefinitionBridge) :
    exactGapValueReal = sInf (B.spine.model.energySpectrum \ ({0} : Set ℝ))

theorem external_audit_readiness_os_wightman_definition_bridge_pvm_detects_first_excitation
    (B : OSWightmanMassGapDefinitionBridge) :
    ∃ ψ : B.spine.model.H,
      ψ ∈ B.spine.model.spectralPVM ({B.spine.model.firstExcitation} : Set ℝ)
```

## Euclidean measure to positive mass gap pipeline

```lean
structure EuclideanYangMillsMeasurePackage where
  configurationSpace : Type
  [instMeasurableSpace : MeasurableSpace configurationSpace]
  euclideanMeasure : MeasureTheory.Measure configurationSpace
  gaugeGroup : Type
  fieldAlgebra : Type
  schwingerFunctions : ℕ → Type
  gaugeGroupCompact : Prop
  gaugeGroupNontrivial : Prop
  reflectionPositive : Prop
  euclideanInvariant : Prop
  symmetric : Prop
  clusterProperty : Prop
  regularity : Prop

structure EuclideanYangMillsMeasureMassGapPipeline where
  euclideanToOSWightman : EuclideanYangMillsMeasureToOSWightmanBridge
  definitionBridge : OSWightmanMassGapDefinitionBridge
  measureReady : euclideanToOSWightman.measure.ready
  bridge_uses_reconstructed_axioms :
    definitionBridge.spine.axioms = euclideanToOSWightman.axioms

theorem euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    P.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf P.nonVacuumHamiltonianSpectrum
```

Route:

```text
Euclidean Yang--Mills measure
→ Osterwalder--Schrader assumptions
→ OS reconstruction
→ Wightman theory
→ physical Hilbert space
→ Hamiltonian as time-translation generator
→ vacuum Ω
→ spectrum of H away from the vacuum energy
→ Δ > 0
```

## Unconditional construction target

```lean
structure EuclideanYangMillsMeasureUnconditionalConstructionTarget where
  measurePackage : EuclideanYangMillsMeasurePackage
  bridge : EuclideanYangMillsMeasureToOSWightmanBridge
  definitionBridge : OSWightmanMassGapDefinitionBridge
  measurePackage_identified : bridge.measure = measurePackage
  bridge_uses_definition_axioms : definitionBridge.spine.axioms = bridge.axioms
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
  reflectionPositivityTheorem : measurePackage.reflectionPositive
  clusterPropertyTheorem : measurePackage.clusterProperty

theorem euclidean_yang_mills_unconditional_target_ready
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    C.ready

theorem euclidean_yang_mills_unconditional_measure_construction_mass_gap
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    C.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf C.toPipeline.nonVacuumHamiltonianSpectrum
```

## Finite-volume / continuum measure construction spine

```lean
structure EuclideanYangMillsFiniteVolumeApproximation where
  index : Type
  finiteVolumeConfiguration : index → Type
  finiteVolumeMeasurableSpace :
    (i : index) → MeasurableSpace (finiteVolumeConfiguration i)
  finiteVolumeMeasure :
    (i : index) → @MeasureTheory.Measure
      (finiteVolumeConfiguration i) (finiteVolumeMeasurableSpace i)
  gaugeInvariantFiniteVolume : Prop
  gaugeInvariantFiniteVolume_proof : gaugeInvariantFiniteVolume
  finiteVolumeReflectionPositive : Prop
  finiteVolumeReflectionPositive_proof : finiteVolumeReflectionPositive

structure EuclideanYangMillsContinuumMeasureConstructionSpine where
  finiteVolume : EuclideanYangMillsFiniteVolumeApproximation
  measurePackage : EuclideanYangMillsMeasurePackage
  projectiveConsistency : Prop
  projectiveConsistency_proof : projectiveConsistency
  tightness : Prop
  tightness_proof : tightness
  weakLimitExists : Prop
  weakLimitExists_proof : weakLimitExists
  continuumMeasureIdentified : Prop
  continuumMeasureIdentified_proof : continuumMeasureIdentified
  schwingerFunctionsAreContinuumLimits : Prop
  schwingerFunctionsAreContinuumLimits_proof : schwingerFunctionsAreContinuumLimits
```

The spine converts into the unconditional target:

```lean
def EuclideanYangMillsContinuumMeasureConstructionSpine.toUnconditionalTarget
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsMeasureUnconditionalConstructionTarget
```

It exposes readiness and Wightman data:

```lean
theorem euclidean_yang_mills_continuum_spine_os_axioms_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.axioms.ready

theorem euclidean_yang_mills_continuum_spine_wightman_theory
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.axioms.wightmanLocality ∧
    S.definitionBridge.spine.axioms.wightmanCovariance ∧
    S.definitionBridge.spine.axioms.wightmanSpectrumCondition
```

It exposes the spectral mass-gap stage:

```lean
theorem euclidean_yang_mills_continuum_spine_positive_hamiltonian_spectrum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∀ E : ℝ, E ∈ S.definitionBridge.spine.model.energySpectrum → 0 ≤ E

theorem euclidean_yang_mills_continuum_spine_vacuum_isolated
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ δ : ℝ, 0 < δ ∧
      Set.Ioo 0 δ ∩ S.definitionBridge.spine.model.energySpectrum = ∅

theorem euclidean_yang_mills_continuum_spine_first_excitation_pvm_detected
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)

theorem euclidean_yang_mills_finite_volume_continuum_construction_mass_gap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum
```

## Construction-spine external audit bridge

The file `EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean` projects
the finite-volume/continuum spine into the existing OS/Wightman external audit
surface:

```lean
def ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop

theorem external_audit_readiness_euclidean_yang_mills_construction_spine_projection
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection S
```

The exact external-audit consequences are also named:

```lean
theorem external_audit_readiness_euclidean_construction_spine_exact_gap_positive
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    0 < exactGapValueReal

theorem external_audit_readiness_euclidean_construction_spine_exact_gap_threshold
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))

theorem external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.firstExcitation} : Set ℝ)
```

The certificate
`ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate` records
limit readiness, measure readiness, OS/Wightman readiness, the external
OS/Wightman projection, exact positivity, exact threshold identity, and PVM
first-excitation detection.

## Proof route summary

```text
finite-volume Mathlib measures
→ projective consistency / tightness / weak limit
→ continuum Euclidean Yang--Mills measure package
→ measure and bridge readiness
→ OS/Wightman readiness
→ Wightman locality / covariance / spectrum condition
→ reconstructed Hilbert space / Hamiltonian / vacuum spectral point
→ positive Hamiltonian spectrum
→ vacuum isolation
→ first excitation detected by the spectral PVM
→ model-level mass-gap predicate
→ exact normalized threshold identity
→ external audit construction-spine projection
→ Δ > 0
```

## Boundary

The remaining hard part is the construction of such a concrete Euclidean
Yang--Mills measure, reconstruction spine, and mass-gap definition bridge from
Yang--Mills theory.  These files are theorem-level closure targets into which
that construction should plug; they are not substitutes for the construction and
do not by themselves provide external mathematical acceptance.

Boundary anchor: the construction-spine external-audit projection is a review route, not external acceptance.
Boundary anchor: external acceptance of the construction-spine external-audit projection is not claimed.
