# Axiomatic Yang--Mills Mass Gap Proof Record

This note records the root proof route for closing the 4D Yang--Mills mass gap development in this repository.  It is intentionally not a local CI workaround and not a literal value assignment for `exactGapValueReal`.  The goal is to replace `True` / `Prop` / `ready` / `receipt`-style terminal objects with explicit theorem objects over Mathlib-compatible mathematical carriers.

## 1. Current boundary

The repository currently treats the development as an internal Lean replay and terminal-audit surface.  Therefore, any final public statement must continue to distinguish internal formal closure from external mathematical consensus.

The previous exact-value route must not define the mass gap by simply choosing `((11 : ℝ) * 3) / 20` or by proving `33 / 20` from a witness chosen only for that purpose.  Such a route is definitionally pinned and is not acceptable for the R6 non-definitional derivation goal.

The correct direction is:

```text
Wightman / Osterwalder--Schrader axioms
→ gauge-field model
→ reconstructed Hilbert space
→ vacuum vector
→ energy-momentum representation
→ self-adjoint Hamiltonian
→ spectral measure / PVM
→ isolated vacuum
→ positive first excitation energy
→ mass gap
→ exactGapValueReal as a theorem-derived spectral value
```

## 2. Non-definitional exact value policy

`exactGapValueReal` should be a projection from a Hamiltonian/PVM/spectral theorem package, not a closed-form rational constant introduced by definition.

Acceptable shape:

```lean
noncomputable def exactGapValueReal : ℝ :=
  hamiltonianPVMSpectralExactGapValue.derivedHamiltonianSpectralValue
```

and then theorem-level facts:

```lean
theorem exact_gap_value_is_spectral_first_excitation :
    exactGapValueReal = M.firstExcitation := ...

theorem exact_gap_value_positive_from_spectrum :
    0 < exactGapValueReal := ...
```

Unacceptable shape:

```lean
noncomputable def exactGapValueReal : ℝ := (33 : ℝ) / 20
```

or an equivalent hidden `Classical.choose` witness whose only mathematical content is the same literal value.

## 3. Root axiomatic carrier

Introduce an explicit model carrier, for example:

```lean
structure FourDimensionalYangMillsAxiomaticModel where
  spacetimeDim : ℕ
  spacetimeDim_eq_four : spacetimeDim = 4

  gaugeGroup : Type
  gaugeGroupCompact : Prop
  gaugeGroupNontrivial : Prop

  euclideanFieldConfiguration : Type
  schwingerFunction : ℕ → Type
  osReflectionPositive : Prop
  osEuclideanInvariant : Prop
  osSymmetric : Prop
  osClusterProperty : Prop
  osRegularity : Prop

  reconstructedHilbertSpace : Type
  vacuum : reconstructedHilbertSpace
  hamiltonian : reconstructedHilbertSpace → reconstructedHilbertSpace
  energySpectrum : Set ℝ
  spectralPVM : Set ℝ → Prop

  vacuumEnergy_mem : (0 : ℝ) ∈ energySpectrum
  positiveEnergy : ∀ E : ℝ, E ∈ energySpectrum → 0 ≤ E
  vacuumIsolated : ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (0 : ℝ) δ ∩ energySpectrum = ∅

  firstExcitation : ℝ
  firstExcitation_mem : firstExcitation ∈ energySpectrum
  firstExcitation_pos : 0 < firstExcitation
  firstExcitation_is_infimum :
    firstExcitation = sInf (energySpectrum \ {0})
```

This is still an interface unless its fields are constructed from Mathlib-backed objects.  The important correction is that each terminal theorem should project from this structure or from a theorem built over this structure, rather than from a bare `ready` token.

## 4. Wightman / OS bridge

The formal proof route should separate two equivalent reconstruction lanes.

### OS lane

```text
Euclidean Schwinger functions
+ OS reflection positivity
+ Euclidean covariance
+ symmetry
+ clustering / regularity
⇒ reconstructed Hilbert space
⇒ vacuum vector
⇒ semigroup generator H
⇒ positive Hamiltonian spectrum
```

Required Lean targets:

```lean
theorem os_reconstructs_hilbert_space
    (M : FourDimensionalYangMillsAxiomaticModel) :
    Nonempty M.reconstructedHilbertSpace := ...

theorem os_reconstructs_vacuum
    (M : FourDimensionalYangMillsAxiomaticModel) :
    ∃ Ω : M.reconstructedHilbertSpace, Ω = M.vacuum := ...

theorem os_reconstructs_positive_hamiltonian
    (M : FourDimensionalYangMillsAxiomaticModel) :
    ∀ E : ℝ, E ∈ M.energySpectrum → 0 ≤ E := ...
```

### Wightman lane

```text
Wightman fields
+ Poincaré covariance
+ locality
+ spectral condition
+ unique vacuum
⇒ Hilbert space representation
⇒ energy-momentum spectrum
⇒ Hamiltonian spectral gap
```

Required Lean targets:

```lean
theorem wightman_spectral_condition_gives_positive_energy
    (M : FourDimensionalYangMillsAxiomaticModel) :
    ∀ E : ℝ, E ∈ M.energySpectrum → 0 ≤ E := ...

theorem vacuum_isolation_gives_mass_gap
    (M : FourDimensionalYangMillsAxiomaticModel) :
    M.vacuumIsolated → 0 < M.firstExcitation := ...
```

## 5. Hamiltonian/PVM/spectral closure

The Hamiltonian/PVM layer should provide the bridge from physical axioms to the exact value carrier.

Required objects:

```lean
structure HamiltonianSpectralMassGapPackage where
  H : Type
  hamiltonian : H → H
  spectrum : Set ℝ
  spectralPVM : Set ℝ → Prop
  vacuumEnergy : ℝ
  firstExcitation : ℝ
  positiveEnergy : ∀ E : ℝ, E ∈ spectrum → 0 ≤ E
  vacuumEnergy_zero : vacuumEnergy = 0
  firstExcitation_mem : firstExcitation ∈ spectrum
  firstExcitation_pos : 0 < firstExcitation
  firstExcitation_is_gap : firstExcitation = sInf (spectrum \ {0})
```

Then the final exact-value route should be theorem-derived:

```lean
theorem hamiltonian_pvm_spectral_package_forces_exact_gap
    (P : HamiltonianSpectralMassGapPackage) :
    exactGapValueReal = P.firstExcitation := ...

theorem hamiltonian_pvm_spectral_package_forces_positive_gap
    (P : HamiltonianSpectralMassGapPackage) :
    0 < exactGapValueReal := by
  rw [hamiltonian_pvm_spectral_package_forces_exact_gap P]
  exact P.firstExcitation_pos
```

## 6. What must be replaced

The following patterns should not serve as final proof closure:

```lean
ready : Prop
receipt : Prop
publicBoundaryHeld : Prop
finalReleaseHeld : Prop
exactValuePreserved : exactGapValueReal = exactGapValueReal
```

They may remain as audit metadata, but they must not be the mathematical endpoint.

Replace them with theorem-level projections:

```lean
external_audit_hilbert_space_constructed : Nonempty M.reconstructedHilbertSpace
external_audit_hamiltonian_constructed : SelfAdjointLike M.hamiltonian
external_audit_energy_spectrum_positive : ∀ E, E ∈ M.energySpectrum → 0 ≤ E
external_audit_vacuum_isolated : ∃ δ, 0 < δ ∧ Set.Ioo 0 δ ∩ M.energySpectrum = ∅
external_audit_mass_gap_positive : 0 < exactGapValueReal
external_audit_exact_value_spectral_origin : exactGapValueReal = M.firstExcitation
```

## 7. Closure criterion

The proof is internally closed only when the external audit readiness gate is no longer a conjunction of audit receipts, but a record containing explicit mathematical theorem fields:

1. a 4D spacetime condition,
2. a compact nontrivial gauge group,
3. OS or Wightman axioms,
4. Hilbert-space reconstruction,
5. vacuum construction,
6. self-adjoint Hamiltonian construction,
7. spectral/PVM construction,
8. positive-energy spectrum,
9. isolated vacuum,
10. positive first excitation,
11. identification of `exactGapValueReal` with the first excitation.

## 8. Immediate Lean implementation plan

1. Add `MGAP4D/MathlibAnalytic/AxiomaticYangMillsModel.lean`.
2. Add OS and Wightman predicate structures.
3. Add `HamiltonianSpectralMassGapPackage` as the theorem-level carrier for mass gap.
4. Refactor `ExternalAuditReadinessGate.lean` so that it imports the axiomatic model and exposes theorem projections rather than bare `ready` receipts.
5. Keep audit fields such as `externalConsensusNotClaimed` as boundary metadata only.
6. Keep `33 / 20` outside the definition of `exactGapValueReal`; if it appears, it must appear only as a theorem consequence of the spectral package.

## 9. Non-claim

This record does not claim that the Clay Yang--Mills mass gap problem is externally solved.  It records the root formal route required for a non-definitional Lean closure of the current repository development.
