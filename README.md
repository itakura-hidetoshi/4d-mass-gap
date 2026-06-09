# MGAP4D

**MGAP4D** is the canonical Lean 4 repository for Hidetoshi Itakura's normalized four-dimensional mass-gap proof architecture.

This repository is the GitHub-native replay and review surface for the MGAP4D line: Lean source, Lake configuration, theorem-surface maps, audit scripts, physical-normalization ledgers, external-review packets, and independent replay instructions are kept in one source tree.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. KuuOS documents do not replace this repository as the canonical Lean source, and they do not independently supply external mathematical consensus.

---

## Status as of 2026-06-09

The current `main` branch records a **Lean 4 proof-carrying terminal discharge chain through R1--R7** for the normalized four-dimensional mass-gap route.

The previous README was stale: R7 is no longer merely downstream.  The current repository contains:

```text
R1 concrete real Hilbert substrate: discharged in the hard-residual ledger
R2 dense-domain unbounded-operator lane: discharged in the hard-residual ledger
R3 Mathlib adjoint/self-adjointness theorem lane: discharged in the hard-residual ledger
R4 genuine-PVM law components: visible at the R5/R6/R7 handoff boundary
R5 compact centered plaquette observable: discharged into the downstream chain
R6 non-definitional exact atom 33/20: discharged
R7 positive spectral-weight witness: discharged
R1--R7 terminal discharge chain index: ready
terminal audit receipt: ready
```

The central Lean-proved value is:

```text
MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
Delta_norm = 33/20
```

The terminal chain also carries positive spectral weight:

```text
MGAP4D.Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

Current conservative public wording:

```text
MGAP4D provides a Lean 4 proof-carrying and replayable audit surface for a
normalized 4D mass-gap route.  The internal terminal R1--R7 discharge chain
carries exact value 33/20 and a positive spectral-weight witness.
External mathematical consensus and Clay-style public acceptance are separate
review processes and are not claimed by documentation alone.
```

---

## Claim boundary

This repository currently claims, at the repository-surface level:

```text
Lean 4 / Lake replay surface: present
exact normalized value theorem body: exactGapValueReal = (33 : ℝ) / 20
physical Hamiltonian scalar normalization: present
physical Hamiltonian operator normalization: present
continuum-Hamiltonian derivation surfaces: present
R1 concrete Hilbert closure: present in terminal ledger
R2 dense-domain operator closure: present in terminal ledger
R3 theorem/self-adjointness discharge: present in terminal ledger
R4 genuine-PVM closure: present in terminal ledger
R4 actual-Borel carrier/wrapper surfaces: present
R4 PVM law components: endpoint laws, projection laws, finite additivity, operator-topology countable additivity
R5 compact centered plaquette observable closure: present
R6 non-definitional exact atom 33/20 closure: present
R7 positive spectral-weight closure: present
R1--R7 terminal discharge chain index: ready
terminal discharge audit receipt: ready
```

It does **not** claim by documentation alone:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI success replaces mathematical proof review
that audit scripts replace Lean kernel checking
that external-audit readiness equals external audit
that a release note or README is a substitute for theorem bodies
```

Review principle:

```text
Lean theorem bodies are the authority inside this repository.
Documentation must track theorem bodies, not downgrade them and not overstate them.
The internal terminal R1--R7 discharge is present.
External public acceptance remains a separate review process.
The normalized value 33/20 is dimensionless until a positive physical scale E0 is chosen.
```

---

## Physical normalization

The normalized theorem-body value is dimensionless.

```text
H_norm = E0^{-1} * H_phys
H_phys = E0 * H_norm

normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap

Delta_norm = 33/20
Delta_phys(E0) = E0 * (33/20)
```

In internal normalized units:

```text
E0 = 1
Delta_phys(1) = 33/20
```

Therefore `33/20` is the dimensionless spectral gap value of the normalized physical-Hamiltonian surface. A dimensional physical mass gap requires an external positive reference scale `E0`.

---

## Active Lean roots and terminal proof surfaces

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
MGAP4D/R4/TheoremSurface.lean
MGAP4D/R5/TheoremSurface.lean
MGAP4D/R6/Theorem.lean
MGAP4D/R7/Theorem.lean
MGAP4D/R7/TheoremSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.lean
```

Pinned toolchain / dependency lane:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

The top-level Lake roots are `MGAP4D` and `MGAP4D.MathlibAnalytic`. The R1--R7 terminal discharge chain is imported through the MGAP4D root.

---

## One-command replay

From a fresh clone:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
bash scripts/check.sh
```

Manual Lean build:

```bash
lake update
lake build
```

A successful replay means that the pinned Lean/Lake/mathlib environment builds and that the declared audit scripts and theorem-surface checks pass.

A successful replay is evidence for local reproducibility. External mathematical consensus and public problem acceptance are still separate review processes.

---

## Current proof route

The current route can be read as:

```text
Exact normalized value / real positivity
  -> gap infimum / Rayleigh lower bound / Rayleigh attainment
  -> spectral mass / exact gap analytic closure
  -> Hilbert, H_phys, spectral theorem, PVM, observable interfaces
  -> continuum-Hamiltonian derivation surfaces
  -> R1 concrete Hilbert closure
  -> R2 dense-domain unbounded-operator closure
  -> R3 Mathlib adjoint/self-adjointness theorem discharge
  -> R4 genuine PVM construction and law components
  -> R5 compact centered plaquette observable closure
  -> R6 non-definitional exact atom 33/20 closure
  -> R7 positive spectral-weight closure
  -> R1--R7 terminal discharge chain index
  -> terminal discharge audit receipt
```

The important current transition is no longer “R7 later”.  The current terminal chain is:

```text
R4 genuine-PVM law components
  -> R5 plaquette observable closure
  -> R6 exact atom 33/20 closure
  -> R7 positive spectral-weight closure
  -> terminal audit receipt
```

---

## R4 genuine-PVM law-component front

Representative files:

```text
MGAP4D/R4/TheoremSurface.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMLawComponentsForR5.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR6ExactAtomBridge.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMLawComponentsToR7PositiveWeightBridge.lean
```

Current R4 terminal-visible surfaces:

```text
actual-Borel carrier/wrapper surfaces
endpoint laws: empty maps to zero and univ maps to identity
projection idempotence laws
intersection/multiplicativity laws
disjoint-union pointwise additivity
operator-topology countable-additivity / convergence theorem
no-shell-to-full-collapse boundary preserved at downstream layers
```

The R4 law components are carried to R6 and R7 rather than being left as an open placeholder.

---

## R5 compact centered plaquette observable front

Representative files:

```text
MGAP4D/R5/TheoremSurface.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableReviewReadyDirectProof.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableDirectProofFinalExport.lean
MGAP4D/R5/Theorem/CompactCenteredPlaquetteObservableDirectProofDownstreamInputContract.lean
MGAP4D/HardPhysicalResidualLedgerR4GenuinePVMDischargedR5PlaquetteObservableClosure.lean
```

Current R5 completed surfaces:

```text
review-ready surface decomposed directly with rcases
compact support / centered / smeared laws extracted from theorem bodies
chosen-observable equality used by rewrite, not documentation shortcut
observable-atom chosen observable receives the same laws by transport
R5 plaquette-observable closure discharged after R4 genuine PVM handoff
```

---

## R6 exact atom 33/20 front

Representative files:

```text
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/R6/Theorem/ExactAtom3320DirectReviewBridge.lean
MGAP4D/HardPhysicalResidualLedgerR5PlaquetteObservableDischargedR6ExactAtomClosure.lean
```

Current R6 completed surfaces:

```text
exact atom 33/20 is derived through the observable-atom theorem body
exactGapValueReal = (33 : ℝ) / 20 is exposed as a theorem
exactGapValueReal belongs to the singleton observable atom
R6 non-definitional exact atom closure is discharged
positive spectral weight remains separately discharged by R7
```

Key one-line theorem:

```lean
theorem exact_atom_3320_value_eq :
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
```

---

## R7 positive spectral-weight front

Representative files:

```text
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightBridge.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotClosure.lean
MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotProjections.lean
MGAP4D/HardPhysicalResidualLedgerR6ExactAtomDischargedR7PositiveWeightClosure.lean
```

Current R7 completed surfaces:

```text
R6 exact atom 33/20 is bridged to the positive spectral-weight witness
observableSpectralWeight3320Certificate.ready is consumed
massWitness.positiveMass = true is proved
exactGapValueReal = (33 : ℝ) / 20 is retained
exactGapValueReal atom membership is retained
witness sector is orthogonal and non-vacuum
R7 positive spectral-weight closure is discharged
```

Key payload theorem:

```lean
theorem atom_exact_r6_direct_positive_weight_review_surface_payload :
  observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  exactGapValueReal ∈ singletonObservableAtomTheoremTheoremData.atom ∧
  witnessSector = orthogonal ∧ witnessSector ≠ vacuum
```

---

## Terminal R1--R7 discharge chain

Representative files:

```text
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.lean
MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean
MGAP4D/HardPhysicalResidualLedgerR1R7ExternalAuditHandoff.lean
```

Current terminal completed surfaces:

```text
R1--R7 terminal discharge chain index is ready
exact value 33/20 and positive spectral weight are carried together
R4 countable-additivity/operator-topology convergence remains visible at terminal level
R4 no-shell boundary remains visible at terminal level
terminal discharge audit receipt is ready
final-release hold and public-boundary lock remain explicit repository governance gates
```

Key terminal theorem:

```lean
theorem hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight :
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true
```

---

## Audit and review entry points

Recommended external review order:

1. Run `bash scripts/check.sh` from a fresh clone.
2. Run `lake build`.
3. Read `THEOREM_INDEX.md`.
4. Read `EXTERNAL_AUDIT_PACKET.md`.
5. Read `INDEPENDENT_REPLAY.md`.
6. Inspect `PHYSICAL_REALIZATION_BOUNDARY.md` for dimensional normalization.
7. Inspect the R4 genuine-PVM law component files.
8. Inspect the R5 plaquette-observable closure files.
9. Inspect the R6 exact atom `33/20` files.
10. Inspect the R7 positive spectral-weight files.
11. Inspect the terminal R1--R7 discharge chain and audit receipt.
12. Record review notes append-only.

Core commands and files:

| Entry point | Role |
|---|---|
| `bash scripts/check.sh` | Complete local replay path. |
| `lake build` | Lean kernel build gate for configured roots. |
| `THEOREM_INDEX.md` | Theorem / bridge / target surface map. |
| `EXTERNAL_AUDIT_PACKET.md` | Top-level external review packet. |
| `INDEPENDENT_REPLAY.md` | Fresh-clone replay procedure. |
| `PHYSICAL_REALIZATION_BOUNDARY.md` | Boundary for physical interpretation. |
| `MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean` | R6 exact atom `33/20`. |
| `MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightBridge.lean` | R7 positive-weight bridge. |
| `MGAP4D/R7/Theorem/AtomExactR6DirectPositiveWeightSlotClosure.lean` | R7 review slot closure. |
| `MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean` | Terminal R1--R7 discharge chain. |
| `MGAP4D/HardPhysicalResidualLedgerTerminalDischargeAuditReceipt.lean` | Terminal audit receipt. |

---

## Repository layout

```text
MGAP4D/              Active Lean source tree
MGAP4D.lean          Top-level Lean import root
docs/                Documentation, ledgers, audit packets, review surfaces
maps/                Lightweight source and dependency maps
scripts/             Local and CI audit scripts
.github/workflows/   GitHub Actions CI
CITATION.cff         Citation metadata
README.md            Repository entry point
ROADMAP.md           Development and audit roadmap
```

---

## Citation

Repository citation metadata is provided in `CITATION.cff`.

```text
Title: MGAP4D: Lean 4 Proof Architecture for a Normalized 4D Mass Gap Theorem
Author: Hidetoshi Itakura
Version: v1.6-dev
DOI: 10.5281/zenodo.20181046
License: CC-BY-4.0
```

The DOI-backed Zenodo record is a proof-architecture and external-audit preparation report. It should be kept synchronized with any audit-oriented tag.

---

## Contribution and review policy

External contributions are most useful when they improve one of the following:

```text
fresh-clone replay
Lean kernel checking
theorem-surface inspection
R4 genuine-PVM law-component review
R5 plaquette-observable closure review
R6 exact atom 33/20 review
R7 positive spectral-weight review
terminal R1--R7 discharge-chain review
terminal audit receipt review
physical-normalization review
continuum-Hamiltonian review
audit-script precision
documentation consistency
external mathematical review
```

Do not treat documentation, CI ledgers, audit scripts, or release notes as substitutes for Lean kernel checking and mathematical proof review.
