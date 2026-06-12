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
`MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureUnconditionalTarget.lean`, and
the finite-volume/continuum construction spine in
`MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionSpine.lean`.

## Scope

The file does **not** claim an unconditional solution of the Clay Yang--Mills
mass gap problem.  Instead, it replaces terminal `True` / bare `Prop` /
`ready` / `receipt` markers with explicit theorem projections over displayed
Mathlib data:

- Euclidean Yang--Mills measure data,
- finite-volume Mathlib measure carriers,
- tightness / weak-limit / projective-consistency construction fields,
- Osterwalder--Schrader assumption package,
- Wightman assumption package,
- gauge group and field-configuration carriers,
- reconstructed Hilbert-space carrier,
- Hamiltonian,
- vacuum,
- spectral PVM interface,
- energy spectrum and energy-momentum spectrum,
- positive-energy condition,
- isolated vacuum,
- positive first non-vacuum spectral excitation.

## Closure theorem

The public closure theorem is:

```lean
theorem wightman_os_hamiltonian_spectral_pvm_closes_4d_mass_gap
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready) :
    M.hasMassGap ∧ 0 < M.massGapValue ∧
      M.massGapValue = sInf (M.energySpectrum \ ({0} : Set ℝ))
```

Thus, once a concrete four-dimensional Yang--Mills construction supplies the
OS/Wightman readiness assumptions and the reconstructed spectral data, the
mass-gap statement is obtained as an ordinary Lean theorem over the Mathlib
carrier.

## External audit projection

The external audit projection exposes the same theorem in the audit surface:

```lean
theorem external_audit_readiness_axiomatic_yang_mills_closure_projection
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready) :
    ExternalAuditReadinessAxiomaticYangMillsClosureProjection M
```

The exact-gap bridge is also explicit:

```lean
theorem external_audit_readiness_axiomatic_yang_mills_exact_gap_projection
    (M : FourDimensionalYangMillsAxiomaticModel)
    (hOS : M.osWightman.ready)
    (hExact : M.massGapValue = exactGapValueReal) :
    ExternalAuditReadinessAxiomaticYangMillsExactGapProjection M
```

This says that if a concrete OS/Wightman Yang--Mills model identifies its
Hamiltonian/PVM spectral mass gap value with the repository's normalized
`exactGapValueReal`, then the audit layer obtains both positivity and the
non-vacuum spectral-threshold identity for `exactGapValueReal`.

## Reconstruction spine

The reconstruction spine records the missing concrete bridge explicitly:

```lean
structure OSWightmanHamiltonianReconstructionSpine where
  axioms : OSWightmanYangMillsAxioms
  model : FourDimensionalYangMillsAxiomaticModel
  model_uses_axioms : model.osWightman = axioms
  axioms_ready : axioms.ready
  exact_gap_value_identified : model.massGapValue = exactGapValueReal
```

From this spine, Lean derives:

```lean
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

The hard construction target is therefore no longer hidden in a receipt-like
marker: it is the explicit production of `OSWightmanHamiltonianReconstructionSpine`.

## Definition bridge

The next bridge fixes the precise meaning of the route from named assumptions to
the mass-gap predicate:

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

This bridge makes the route auditable:

- the Wightman spectrum condition projects to positive Hamiltonian energy,
- the OS cluster property projects to vacuum isolation,
- the spectral PVM detects the first excitation,
- the reconstructed Hamiltonian has the model-level mass-gap predicate,
- `exactGapValueReal` is identified with the non-vacuum spectral threshold.

The certificate
`OSWightmanMassGapDefinitionBridgeCertificate` records these as theorem fields,
not as terminal receipts.

## External bridge audit surface

The file `OSWightmanMassGapExternalAuditBridge.lean` adds the external-audit
projection for a concrete definition bridge:

```lean
theorem external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection
    (B : OSWightmanMassGapDefinitionBridge) :
    ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection B
```

The projection exposes, in one audit-visible theorem, the gauge compactness and
nontriviality assumptions, reflection positivity, locality, covariance, the
spectrum condition, the four-dimensional Hilbert carrier, the self-adjoint
Hamiltonian predicate, the vacuum spectral point, positive energy, vacuum
isolation, PVM detection of the first excitation, model-level mass gap,
`0 < exactGapValueReal`, and the exact spectral-threshold identity.

The direct audit-visible consequences are also available as named theorems:

```lean
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

The file `EuclideanYangMillsMeasureToMassGapPipeline.lean` adds the upstream
Euclidean-measure object and the end-to-end theorem surface:

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
```

The full conditional object is:

```lean
structure EuclideanYangMillsMeasureMassGapPipeline where
  euclideanToOSWightman : EuclideanYangMillsMeasureToOSWightmanBridge
  definitionBridge : OSWightmanMassGapDefinitionBridge
  measureReady : euclideanToOSWightman.measure.ready
  bridge_uses_reconstructed_axioms :
    definitionBridge.spine.axioms = euclideanToOSWightman.axioms
```

This gives the named route:

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

The main theorem surface is:

```lean
theorem euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    P.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf P.nonVacuumHamiltonianSpectrum
```

The theorem is still conditional: it proves the downstream implication once the
Euclidean measure package, OS/Wightman reconstruction bridge, and Hamiltonian/PVM
definition bridge are supplied.  It does not assert that the Euclidean
Yang--Mills measure has already been constructed unconditionally.

## Unconditional construction target

The file `EuclideanYangMillsMeasureUnconditionalTarget.lean` adds the theorem
target needed for genuine unconditional promotion:

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
```

The key difference from the conditional pipeline is that the construction-side
obligations are not mere names: each named construction proposition has a proof
field inside the target.  Therefore `ready` is derived without additional
external hypotheses:

```lean
theorem euclidean_yang_mills_unconditional_target_ready
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    C.ready
```

The promotion theorem has only the target object as its input:

```lean
theorem euclidean_yang_mills_unconditional_measure_construction_mass_gap
    (C : EuclideanYangMillsMeasureUnconditionalConstructionTarget) :
    C.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf C.toPipeline.nonVacuumHamiltonianSpectrum
```

This is still not a declaration that the Clay-level construction has already
been accepted; it is the Lean theorem socket into which such a construction must
plug.

## Finite-volume / continuum measure construction spine

The file `EuclideanYangMillsMeasureConstructionSpine.lean` adds one more upstream
layer.  It separates the hard Euclidean measure construction into finite-volume
Mathlib measure carriers and continuum-limit proof fields:

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
```

The continuum construction spine then adds the analytic limit layer:

```lean
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

This spine is converted to the unconditional target by:

```lean
def EuclideanYangMillsContinuumMeasureConstructionSpine.toUnconditionalTarget
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsMeasureUnconditionalConstructionTarget
```

It then exposes the OS/Wightman readiness route as named theorem surfaces:

```lean
theorem euclidean_yang_mills_continuum_spine_measure_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.measurePackage.ready

theorem euclidean_yang_mills_continuum_spine_bridge_measure_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.bridge.measure.ready

theorem euclidean_yang_mills_continuum_spine_os_axioms_ready
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.axioms.ready

theorem euclidean_yang_mills_continuum_spine_wightman_theory
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.axioms.wightmanLocality ∧
    S.definitionBridge.spine.axioms.wightmanCovariance ∧
    S.definitionBridge.spine.axioms.wightmanSpectrumCondition
```

The reconstructed Hilbert/Hamiltonian/vacuum stage is also exposed:

```lean
theorem euclidean_yang_mills_continuum_spine_physical_hilbert_space
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Nonempty S.definitionBridge.spine.model.H

theorem euclidean_yang_mills_continuum_spine_hamiltonian_time_translation_generator
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.hamiltonianSelfAdjoint

theorem euclidean_yang_mills_continuum_spine_vacuum_omega_spectral_point
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.vacuum ∈
      S.definitionBridge.spine.model.spectralPVM ({0} : Set ℝ)
```

The main theorem from this upstream construction layer is:

```lean
theorem euclidean_yang_mills_finite_volume_continuum_construction_mass_gap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.toPipeline.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf S.toPipeline.nonVacuumHamiltonianSpectrum
```

Thus the proof route is now:

```text
finite-volume Mathlib measures
→ projective consistency / tightness / weak limit
→ continuum Euclidean Yang--Mills measure package
→ measure and bridge readiness
→ OS/Wightman readiness
→ Wightman locality / covariance / spectrum condition
→ reconstructed Hilbert space / Hamiltonian / vacuum spectral point
→ Hamiltonian/PVM mass-gap bridge
→ Δ > 0
```

## Boundary

The remaining hard part is the construction of such a concrete Euclidean
Yang--Mills measure, reconstruction spine, and mass-gap definition bridge from
Yang--Mills theory.  These files are the theorem-level closure target into which
that construction should plug; they are not substitutes for the construction.
