# Hard Physical Residual Ledger v0.1

This ledger records the current hard residuals that remain after the repository has made the spectral `33/20` route replay-visible at the external-audit and replay-certificate layers.

The purpose is to prevent the public audit surface from being confused with a completed concrete mathematical construction. The current repository has a CI-enforced replay chain for the spectral route, but the following items are still the hard physical/mathematical residuals required for a fully concrete, non-definitional derivation from a physical 4D Yang--Mills continuum Hamiltonian.

## Current replay-visible surface

The current main branch exposes and audits the following route:

```text
Hamiltonian spectral derivation
  -> spectral infimum
  -> spectral attainment
  -> observable spectral atom
  -> positive nonzero spectral mass
  -> PVM public audit projection
  -> external audit readiness gate
  -> replay certificate
```

The following public-audit projection is visible:

```text
externalAuditReadinessPVMSpectralAtomPublicAuditProjection
external_audit_readiness_pvm_spectral_atom_public_audit_projection
external_audit_readiness_pvm_spectral_atom_value_eq_3320
external_audit_readiness_pvm_spectral_atom_positive_nonzero_mass
external_audit_readiness_pvm_spectral_atom_boundary_held
```

This means the route is replay-visible and audit-enforced, not that all concrete analytic constructions below have been discharged.

## Internal R1--R7 discharge spine v0.1

The current main branch also carries an internal Lean-side discharge/index spine for the user-facing R1--R7 residual names:

```text
MGAP4D/ConcreteR1R7ResidualDischarge.lean
```

The spine is additive to the prior theorem-obligation and public-audit layers. It binds the user-facing concrete residual names to the existing replay-visible completion and continuum spectral derivation without opening the final-release boundary:

```text
ConcreteR1R7ResidualDischarge
concreteR1R7ResidualDischarge3320
concrete_r1r7_residual_discharge_3320_ready
concrete_r1r7_residual_discharge_exact_gap_value_3320
concrete_r1r7_residual_discharge_positive_nonzero_spectral_mass
concrete_r1r7_residual_discharge_final_release_held
concrete_r1r7_residual_discharge_public_boundary_locked
```

The seven user-facing residual targets are now represented in that discharge spine in the same order as the required future spine:

```text
ConcreteRealHilbertSpace
  -> DenseDomainUnboundedHamiltonian
  -> SelfAdjointPhysicalHamiltonian
  -> ConcretePVMSpectralMeasure
  -> CompactCenteredPlaquetteObservable
  -> NondefinitionalSpectralAtom3320
  -> PositiveSpectralWeightDerivation3320
```

Interpretation:

```text
internal Lean discharge spine visible / theorem-obligation binding present / exact 33/20 and positive nonzero spectral-mass projections carried / final-release boundary held / public boundary locked
```

The current main branch now also carries a Lean-side bridge from this ledger entry to the internal discharge spine:

```text
MGAP4D/HardPhysicalResidualLedgerR1R7DischargeBridge.lean
HardPhysicalResidualLedgerR1R7DischargeBridge
hardPhysicalResidualLedgerR1R7DischargeBridge3320
hard_physical_residual_ledger_r1r7_discharge_bridge_ready
hard_physical_residual_ledger_r1r7_discharge_bridge_exact_gap_value_3320
hard_physical_residual_ledger_r1r7_discharge_bridge_positive_nonzero_spectral_mass
hard_physical_residual_ledger_r1r7_discharge_bridge_final_release_held
hard_physical_residual_ledger_r1r7_discharge_bridge_public_boundary_locked
hard_physical_residual_ledger_r1r7_discharge_bridge_status_preserved
```

Boundary of this update:

```text
This update records a replay-visible internal discharge/index spine and ledger bridge. It does not assert external consensus, does not unlock public final release, and does not replace the harder Mathlib/operator-theoretic closure conditions listed below.
```

## Hard residuals

### R1. Concrete real Hilbert space on Mathlib

Required target:

```text
A real Hilbert space H implemented as a standard Mathlib Hilbert-space object.
```

Current status:

```text
interface / construction skeleton / replay-visible surface / internal discharge spine binding present
```

Required closure condition:

```text
H is not merely represented by a custom Prop surface;
H has a Mathlib-recognized NormedAddCommGroup, InnerProductSpace ℝ, CompleteSpace, and HilbertSpace-compatible structure.
```

### R2. Densely defined unbounded operator

Required target:

```text
A physical Hamiltonian H_phys defined on a dense domain D(H_phys) ⊂ H.
```

Current status:

```text
unbounded-operator skeleton / domain-preservation surface / internal discharge spine binding present
```

Required closure condition:

```text
D(H_phys) is a concrete dense subspace or dense set;
H_phys is an operator whose graph/domain is represented independently of a theorem statement;
density is derived, not asserted by naming.
```

### R3. Self-adjointness proof

Required target:

```text
SelfAdjoint H_phys
```

Current status:

```text
self-adjointness certificate surface / bridge-adoption surface / internal discharge spine binding present
```

Required closure condition:

```text
symmetry, closedness or essential self-adjointness, and domain equality with the adjoint are derived using Mathlib-compatible operator notions;
self-adjointness is not a field asserted inside a record.
```

### R4. Concrete PVM / spectral measure construction

Required target:

```text
A concrete projection-valued measure E_H associated with H_phys by the spectral theorem.
```

Current status:

```text
PVM interface / spectral theorem replay surface / internal discharge spine binding present
```

Required closure condition:

```text
PVM is constructed from the self-adjoint Hamiltonian through a Mathlib-compatible spectral theorem interface;
measurability, projection law, countable additivity, and support relation to the spectrum are represented explicitly.
```

### R5. Compact centered plaquette observable

Required target:

```text
A compactly supported smeared centered plaquette observable A_{p,g}.
```

Current status:

```text
compact plaquette construction theorem surface / observable atom interface / internal discharge spine binding present
```

Required closure condition:

```text
The observable is built from an explicit local plaquette/smearing construction;
centering is derived by subtracting the vacuum expectation;
compact support or locality is represented in the construction, not only in the name.
```

### R6. Non-definitional derivation of the exact atom 33/20

Required target:

```text
33/20 emerges from the spectrum of H_phys restricted to Ω⊥.
```

Current status:

```text
exact value replay-visible; spectral infimum and attainment theorem surfaces present; internal discharge spine binding present
```

Required closure condition:

```text
33/20 is not introduced by defining exactGapValueReal to be 33/20;
there is an analytic or algebraic chain deriving spectral infimum, eigenvalue/atom localization, and equality to 33/20 from Hamiltonian data.
```

### R7. Nontrivial derivation of positive spectral weight

Required target:

```text
ρ_{A_{p,g}}({33/20}) > 0
```

Current status:

```text
positive nonzero spectral mass replay-visible at public audit projection; internal discharge spine binding present
```

Required closure condition:

```text
positive spectral weight is derived from a nonzero overlap / nonzero spectral projection / cyclic vector / observable localization argument;
positivity is not merely stored as a Prop field in the spectral mass surface.
```

## Required future spine

The next concrete spine should proceed in this order:

```text
ConcreteRealHilbertSpace
  -> DenseDomainUnboundedHamiltonian
  -> SelfAdjointPhysicalHamiltonian
  -> ConcretePVMSpectralMeasure
  -> CompactCenteredPlaquetteObservable
  -> NondefinitionalSpectralAtom3320
  -> PositiveSpectralWeightDerivation3320
```

## Audit boundary

This ledger is additive-only. It does not weaken the current replay-visible chain. It prevents overclaiming by preserving the distinction between:

```text
CI-enforced replay-visible audit surface
```

and

```text
fully concrete non-definitional analytic construction
```

The internal R1--R7 discharge spine narrows the local Lean audit gap by adding explicit replay-visible names and projections, while the harder mathematical closure conditions remain visible until replaced by stronger Mathlib/operator-theoretic constructions.

The hard physical residual ledger bridge adds an explicit Lean-side audit map from this ledger to the current discharge spine, while preserving the same open hard-residual statuses.

## Current status

```text
R1: open / construction-hardening required
R2: open / domain-hardening required
R3: open / self-adjointness-hardening required
R4: open / PVM-construction required
R5: open / observable-construction required
R6: open / non-definitional exact-value derivation required
R7: open / nontrivial positive spectral-weight derivation required
```

## Current internal discharge status

```text
ConcreteR1R7ResidualDischarge: installed / internal discharge spine visible
HardPhysicalResidualLedgerR1R7DischargeBridge: installed / ledger bridge visible
R1--R7 user-facing spine names: bound to replay-visible theorem-obligation completion
Exact 33/20 projection: carried by continuum spectral-complete derivation
Positive spectral-mass projection: carried as positive and nonzero spectral mass
Final-release boundary: held
Public boundary: locked
Hard residual ledger statuses: preserved for stronger future Mathlib/operator-theoretic replacement
```
