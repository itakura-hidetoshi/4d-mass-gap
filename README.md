# MGAP4D

MGAP4D is a Lean 4 repository for developing, checking, and auditing the proof architecture of a normalized 4D mass gap theorem.

This repository is GitHub-native: the active Lean source tree, CI, documentation, theorem-surface checkpoints, bridge audits, and boundary ledgers live directly in this repository.

## Repository role

This repository is the canonical Lean proof repository for the MGAP4D normalized 4D mass gap proof architecture.

KuuOS references this repository as a physics-facing bridge and public-core governance surface:

```text
Canonical proof repo: itakura-hidetoshi/4d-mass-gap
KuuOS reference repo: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS reference documents do not replace this repository as the canonical Lean proof repository and do not independently open final public theorem release.

## Current theorem claim and boundary

### Internal normalized theorem-body claim

Inside the MGAP4D Lean proof architecture, the current theorem-body surface records the normalized exact spectral gap value:

```text
exactGapValueReal = 33 / 20
```

The current repository state treats `33/20` as coming from the theorem-body closure, not from a packaging artifact, documentation artifact, CI ledger, manifest-only wrapper, or prototype-only release wrapper.

This is recorded by:

```text
MGAP4D/MathlibAnalytic/ExactGapTheoremBodyClosure.lean
MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean
docs/mathlib_exact_value_theorem_body_origin.md
docs/mathlib_exact_value_theorem_body_origin_ci.md
```

The theorem-body origin chain explicitly carries:

```text
Hilbert Rayleigh quotient body
self-adjoint H_phys body
spectral theorem body
PVM body
observable atom body
compact plaquette construction body
operator-measure compatibility body
observable spectral weight positivity
PVM mass compatibility
```

### Physical Hamiltonian normalization

The physical Hamiltonian normalization is read through an explicit reference energy scale `E0`:

```text
H_norm = H_phys / E0
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
```

In MGAP4D internal normalized units:

```text
E0 = 1
normalizedGap = exactGapValueReal = 33/20
physicalGap = exactGapValueReal = 33/20
```

For dimensional interpretation:

```text
physicalGap_dimensional = E0 * (33/20)
```

Thus `33/20` is the dimensionless spectral gap of the normalized physical Hamiltonian. A dimensional physical gap requires an external reference scale `E0`.

Relevant files:

```text
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
docs/mathlib_physical_hamiltonian_normalization_bridge.md
docs/mathlib_physical_hamiltonian_normalization_bridge_ci.md
```

### Public boundary

The repository currently claims an internal, normalized, proof-architecture theorem-body surface with CI and bridge-audit support.

It does **not** claim:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI ledgers replace mathematical proof review
that bridge-coherence audit replaces Lean kernel checking
```

The public final theorem boundary remains review-gated pending independent replay and external audit.

## Current active Lean roots

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
```

`MGAP4D.lean` is the top-level Lean import root.

`MGAP4D/MathlibAnalytic.lean` is the internal analytic theorem-surface root. The name `MathlibAnalytic` records the analytic adoption/bridge layer; it does not by itself mean that `main` imports upstream Mathlib directly.

## Main analytic chain

The current analytic bridge chain is:

```text
Concrete Hilbert realization
  -> Concrete H_phys / unbounded-operator realization
  -> Physical unbounded-operator skeleton
  -> Concrete Yang-Mills Hamiltonian skeleton
  -> Spectral realization skeleton
  -> Continuum spectral theorem skeleton
  -> Final theorem release skeleton
  -> Final theorem release closure
  -> Final theorem release chain index
  -> Final theorem release bundle manifest
  -> Concrete residual closure
  -> Physical Hamiltonian normalization bridge
  -> Exact value theorem-body origin certificate
```

Key source files:

```text
MGAP4D/MathlibAnalytic/ConcreteHilbertRealizationTheorem.lean
MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean
MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean
MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean
MGAP4D/MathlibAnalytic/SpectralRealizationSkeleton.lean
MGAP4D/MathlibAnalytic/ContinuumSpectralTheoremSkeleton.lean
MGAP4D/MathlibAnalytic/FinalTheoremReleaseSkeleton.lean
MGAP4D/MathlibAnalytic/FinalTheoremReleaseClosure.lean
MGAP4D/MathlibAnalytic/FinalTheoremReleaseChainIndex.lean
MGAP4D/MathlibAnalytic/FinalTheoremReleaseBundleManifest.lean
MGAP4D/MathlibAnalytic/ConcreteResidualClosure.lean
MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean
```

## Concrete residuals now closed as internal surfaces

The following residual surfaces are closed inside the current internal Lean architecture:

```text
concrete Hilbert realization
concrete H_phys / unbounded-operator realization
spectral measure / PVM exact-atom realization
compact lattice-gauge plaquette observable construction
operator-measure realization and compatibility
physical Hamiltonian normalization bridge
exact-value theorem-body origin certificate
```

Relevant CI/documentation ledgers:

```text
docs/mathlib_concrete_residual_closure.md
docs/mathlib_concrete_residual_closure_ci.md
docs/mathlib_physical_hamiltonian_normalization_bridge.md
docs/mathlib_physical_hamiltonian_normalization_bridge_ci.md
docs/mathlib_exact_value_theorem_body_origin.md
docs/mathlib_exact_value_theorem_body_origin_ci.md
```

Boundary for these closures:

```text
internal concrete residual closure only
theorem-body origin certificate only
normalization bridge only
external consensus is not claimed
public theorem boundary is held
```

## CI and audit status

### Lean Direct Elan CI

Recent direct Lean CI confirmation:

```text
Workflow: Lean Direct Elan CI
Run ID: 25945521468
Audit job ID: 76272692295
Build job ID: 76272703776
Commit checked out by CI: f4837cc92af776036e7c15f4f1ab117cc1b11e77
Result: success
```

Confirmed:

```text
Verify release manifest: success
Audit Lean forbidden tokens: success
Audit major theorem non-placeholder surface: success
Summarize Lean replay surface: success
Build Lean project via direct elan: success
lake build: success
```

Forbidden-token audit:

```text
Lean files scanned: 447
sorry: 0
admit: 0
axiom: 0
constant: 0
```

Major theorem non-placeholder audit:

```text
Major theorem specs audited: 12
Major theorem non-placeholder audit passed
```

### Bridge Coherence CI

Dedicated bridge coherence confirmation:

```text
Workflow: Bridge Coherence CI
Run ID: 25946061297
Job ID: 76274304501
Job name: Check bridge coherence
Commit checked out by CI: fc02308553be06dcb7843f509ccf41bf71cc5e35
Result: success
```

Confirmed:

```text
Check Lean forbidden tokens: success
Check major theorem non-placeholder surface: success
Check analytic bridge coherence: success
Summarize Lean replay surface: success
```

Bridge coherence audit:

```text
Bridge files audited: 7
Ordered import edges audited: 4
Bridge anchors audited: Hilbert, H_phys, Yang-Mills, spectral/PVM, continuum, normalization
Value anchors audited: exact_value_eq_3320 / exactGapValueReal
Boundary anchors audited: publicBoundaryHeld and open-boundary markers
Bridge coherence audit passed
```

Relevant ledgers:

```text
docs/mathlib_major_theorem_nonplaceholder_audit.md
docs/mathlib_major_theorem_nonplaceholder_audit_ci.md
docs/mathlib_bridge_coherence_audit.md
docs/mathlib_bridge_coherence_ci.md
```

## What the audits mean

The current automated audits check that:

```text
major theorem surfaces do not use sorry/admit/axiom/constant
major theorem surfaces are not trivial True-only statements
33/20 theorem-body origin is checked as a non-placeholder statement
operator-measure/PVM compatibility is checked as a non-placeholder statement
Hamiltonian normalization bridge is checked as a non-placeholder statement
Hilbert -> H_phys -> Yang-Mills -> spectral/PVM -> continuum bridge order is mechanically audited
exact value preservation anchors are mechanically audited
public boundary markers are mechanically audited
```

The audits are syntactic/contract checks plus Lean build confirmation. They complement, but do not replace:

```text
Lean kernel checking through lake build
theorem-body proof review
independent replay
external mathematical peer review
```

## Citation and Zenodo record

A DOI-backed technical report for the Phase 3 spectral gap formalization checkpoint is archived on Zenodo:

```text
Hidetoshi Itakura, A Lean 4 Proof Architecture for a Normalized 4D Mass Gap Theorem: Phase 3 Spectral Gap Formalization and External-Audit Boundary, Zenodo, 2026. DOI: 10.5281/zenodo.20181046.
```

```text
Zenodo record: 20181046
DOI: 10.5281/zenodo.20181046
URL: https://zenodo.org/records/20181046
Repository citation metadata: CITATION.cff
Repository receipt: docs/zenodo_record_20181046.md
```

This Zenodo record is a proof-architecture and external-audit preparation report. It does not by itself open public final theorem release.

## External audit packet

External reviewers can start from the top-level audit packet:

```text
EXTERNAL_AUDIT_PACKET.md
```

The packet gives an ordered route through README, the review checklist, independent replay, theorem index, physical-realization boundary, and documentation ledgers.

## Independent replay

External reviewers can reproduce the repository-level replay using:

```text
INDEPENDENT_REPLAY.md
```

The independent replay guide covers:

```text
fresh clone replay
pinned Lean toolchain confirmation
scripts/check.sh one-command replay
manual step-by-step audit replay
GitHub Actions parity
failure interpretation
review boundary
```

## Theorem index

External reviewers can inspect the named theorem and bridge surfaces using:

```text
THEOREM_INDEX.md
```

The theorem index covers:

```text
active Lean roots
12 major theorem surfaces audited for non-placeholder statements
7 analytic / physical bridge surfaces audited for coherence
ordered bridge chain
normalization surface
audit script roles
residual boundary
```

## Physical realization boundary

External reviewers should read the physical-realization boundary before interpreting singleton, `PUnit`, prototype, or skeleton surfaces physically:

```text
PHYSICAL_REALIZATION_BOUNDARY.md
```

That guide clarifies that these surfaces are contract witnesses and review surfaces, not a claim that the final continuum Yang-Mills Hilbert space or spectral measure has been replaced by a one-point model.

## External review checklist

External reviewers can follow the end-to-end review checklist:

```text
EXTERNAL_REVIEW_CHECKLIST.md
```

The checklist bundles the replay guide, theorem index, physical-realization boundary, normalization reading, source/document comparison, and final review notes into one ordered path.

## Build and local checks

Lean build:

```bash
lake update
lake build
```

Full local check script:

```bash
bash scripts/check.sh
```

`bash scripts/check.sh` now runs:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/replay_summary.py
lake update
lake build
```

GitHub Actions workflows:

```text
.github/workflows/lean-direct-elan.yml
.github/workflows/bridge-coherence-ci.yml
```

## Repository layout

```text
MGAP4D/                  Active Lean source tree
MGAP4D.lean              Top-level Lean import root
docs/                    GitHub-native documentation and checkpoint ledger
maps/                    Lightweight source and dependency maps
scripts/                 Local and CI audit scripts
.github/workflows/       GitHub Actions CI
```

## Status summary

```text
GitHub-native Lean project: active
Lean Direct Elan CI: green
Bridge Coherence CI: green
Forbidden Lean tokens: 0 sorry / 0 admit / 0 axiom / 0 constant
Major theorem non-placeholder audit: green
Bridge coherence audit: green
External audit packet: EXTERNAL_AUDIT_PACKET.md
Independent replay guide: INDEPENDENT_REPLAY.md
Theorem index: THEOREM_INDEX.md
Physical realization boundary: PHYSICAL_REALIZATION_BOUNDARY.md
External review checklist: EXTERNAL_REVIEW_CHECKLIST.md
Physical Hamiltonian normalization bridge: CI green
Exact value theorem-body origin: CI green
Concrete residual closure: CI green
Dimensionless normalized exact value surface: 33/20
External consensus: not claimed
Public final theorem claim: review-gated pending independent replay and external audit
```
