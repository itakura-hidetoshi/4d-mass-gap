# Axiomatic Yang--Mills Mass Gap Closure Route

This note records the conditional proof kernel installed in
`MGAP4D/MathlibAnalytic/AxiomaticYangMillsMassGapClosure.lean`, its external
audit projection in
`MGAP4D/MathlibAnalytic/AxiomaticYangMillsExternalAuditProjection.lean`, the
OS/Wightman-to-Hamiltonian reconstruction spine in
`MGAP4D/MathlibAnalytic/OSWightmanHamiltonianReconstructionSpine.lean`, the
OS/Wightman mass-gap definition bridge in
`MGAP4D/MathlibAnalytic/OSWightmanMassGapDefinitionBridge.lean`, and its external
audit projection in
`MGAP4D/MathlibAnalytic/OSWightmanMassGapExternalAuditBridge.lean`.

## Scope

The file does **not** claim an unconditional solution of the Clay Yang--Mills
mass gap problem.  Instead, it replaces terminal `True` / bare `Prop` /
`ready` / `receipt` markers with explicit theorem projections over displayed
Mathlib data:

- Wightman / Osterwalder--Schrader axiom package,
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

The next bridge fixes the precise meaning of the route from named axioms to the
mass-gap predicate:

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

## Boundary

The remaining hard part is the construction of such a concrete spine and
mass-gap definition bridge from Yang--Mills theory.  These files are the
theorem-level closure target into which that construction should plug; they are
not substitutes for the construction.
