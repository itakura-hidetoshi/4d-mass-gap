# MGAP4D

**MGAP4D** is the canonical Lean 4 repository for Hidetoshi Itakura's normalized four-dimensional mass-gap proof architecture.

This repository is the GitHub-native replay and review surface for the MGAP4D line: Lean source, Lake configuration, theorem-surface maps, audit scripts, physical-normalization ledgers, external-review packets, and independent replay instructions are kept in one source tree.

```text
Canonical proof repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

KuuOS may reference MGAP4D as a physics-facing bridge and public-core governance surface. KuuOS documents do not replace this repository as the canonical Lean source, and they do not independently open public final theorem release.

---

## Status as of 2026-06-07

The current `main` branch records an **internal normalized Lean theorem-body / proof-architecture surface** for a normalized 4D mass-gap route.

The active mathematical engineering front has moved from the local finite-supported measurable PVM scaffold into the **R4 actual-Borel spectral-measure/PVM phase**.

Current status, stated conservatively:

```text
internal normalized theorem-body value: 33/20
physical normalization boundary: present
continuum-Hamiltonian proof-architecture surfaces: present
concrete l2 R2 local analytic lane: support/boundary layer, not spectral release
R4 finite-supported measurable local PVM phase: support/boundary layer completed
R4 actual Set ℝ endpoint carrier: present
R4 actual Borel endpoint set algebra: present
R4 actual Borel wrapper / closure phase surfaces: present, boundary-held
full genuine operator-valued spectral measure: not yet claimed
public final theorem acceptance: not claimed
```

The normalized theorem-body value recorded by the Lean route is:

```text
exactGapValueReal = 33 / 20
Delta_norm = 33/20
```

`33/20` is treated as an **internal normalized theorem-body value**. It is not treated as a documentation artifact, CI artifact, manifest-only artifact, release-wrapper artifact, or prototype-only assertion.

Recommended public wording:

```text
MGAP4D provides a Lean 4 proof architecture and replayable audit surface
for an internal normalized 4D mass-gap theorem-body route with normalized value 33/20.
The current active front is the R4 actual-Borel spectral-measure/PVM phase.
Public final theorem acceptance is not claimed.
```

---

## Claim boundary

This repository currently claims, at the repository-surface level:

```text
Lean 4 / Lake replay surface: present
exact normalized value surface: 33/20
physical Hamiltonian scalar normalization: present
physical Hamiltonian operator normalization: present
continuum-Hamiltonian derivation surfaces: present
concrete l2 R2 graph-norm / residual-zero local lane: present, boundary-held
R4 finite-supported measurable local PVM phase: present as scaffold/boundary
R4 actual endpoint carrier in Set ℝ: present
R4 endpoint measurability for ∅ and Set.univ: present
R4 endpoint complement / union / intersection algebra: present
R4 actual Borel wrapper as measurable subsets of ℝ: present as phase surface
R4 Boolean closure witnesses for the actual Borel wrapper: present as phase surface
```

It does **not** claim:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI success replaces mathematical proof review
that audit scripts replace Lean kernel checking
that external-audit readiness equals external audit
that concrete l2 R2 residual-zero audit implies a closed operator theorem
that graph-level formal-adjoint equality implies Mathlib IsSelfAdjoint promotion
that finite-supported local PVM surfaces imply a genuine spectral measure
that endpoint-only Borel surfaces imply arbitrary Borel spectral measure construction
that actual Borel wrapper closure implies operator-topology countable additivity
that the current R4 route already gives exact atom 33/20, positive spectral weight, or a physical Yang-Mills Hamiltonian
```

Review principle:

```text
Lean kernel checking is necessary but not identical with external mathematical consensus.
Replay success is evidence, not peer review.
Documentation must never be treated as a substitute for theorem bodies.
Local finite-supported PVM is scaffold and boundary, not final spectral measure.
Actual Set ℝ / Borel carrier progress is real progress, but not yet operator-valued countable additivity.
R4 PVM progress must not be promoted into R5 plaquette or R7 atom/weight claims prematurely.
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

## Active Lean roots

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
MGAP4D/R4/TheoremSurface.lean
```

Pinned toolchain / dependency lane:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

The top-level Lake roots are `MGAP4D` and `MGAP4D.MathlibAnalytic`. R4 is imported through the MGAP4D root and is the current spectral-measure/PVM hardening front.

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

A successful replay does **not** by itself mean external mathematical consensus, peer-review completion, full PVM construction, or public final theorem acceptance.

---

## Current proof route

The current route can be read as:

```text
Exact normalized value / real positivity
  -> gap infimum / Rayleigh lower bound / Rayleigh attainment
  -> spectral mass / exact gap analytic closure
  -> Hilbert, H_phys, spectral theorem, PVM, observable interfaces
  -> compact plaquette and operator-measure compatibility surfaces
  -> exact gap theorem-body closure
  -> physical Hamiltonian scalar and operator normalization
  -> continuum-Hamiltonian derivation surfaces
  -> concrete l2 R2 local analytic support lane
  -> R4 spectral-measure/PVM operator-valued target surface
  -> finite-supported measurable local PVM scaffold
  -> actual Set ℝ endpoint carrier
  -> actual Borel endpoint set algebra
  -> actual Borel set wrapper
  -> actual Borel set-algebra closure surface
  -> genuine spectral-measure obligations
  -> R5 compact centered plaquette observable / R7 atom-weight route
```

The important current transition is:

```text
local finite-supported PVM scaffold
  -> actual Set ℝ endpoint carrier
  -> actual Borel endpoint set algebra
  -> arbitrary Borel carrier wrapper
  -> Boolean closure witnesses
  -> operator-valued countable additivity and spectral theorem handoff
```

---

## R4 spectral-measure/PVM front

Representative files for the current R4 front:

```text
MGAP4D/R4/TheoremSurface.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelEndpointCarrier.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelEndpointSetAlgebra.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelSetWrapper.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelSetAlgebraClosure.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelPhaseSurface.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelClosurePhaseSurface.lean
```

Current R4 completed/ready surfaces:

```text
finite-supported measurable local PVM support/boundary phase
actual endpoints ∅ and Set.univ as subsets of ℝ
endpoint Borel measurability
endpoint complement / union / intersection laws
actual Borel carrier wrapper {s : Set ℝ // MeasurableSet s}
wrapper complement / union / intersection operations
closure witnesses after forgetting back to Set ℝ
public nonpromotion boundary after each step
```

Still open in R4:

```text
arbitrary Borel API hardening beyond wrapper closure
operator-topology countable additivity
projection-valued spectral-measure construction
self-adjoint spectral theorem handoff
spectral integral compatibility
exact atom 33/20 from the genuine PVM route
positive spectral weight
promotion into R5 compact centered plaquette observable
physical Yang-Mills Hamiltonian promotion
```

---

## Concrete l2 R2 route boundary

The concrete `l2` R2 route remains useful as a local analytic hardening lane. It is not the current main spectral-measure front.

Current local reading:

```text
R2 graph-norm core blocker: closed at the current route layer
R2 residual-zero audit surface: present
formal-adjoint graph / operator-value surface: present
R2 residual taxonomy: active review lane
```

Still boundary-held:

```text
closed operator theorem
Mathlib IsSelfAdjoint theorem
spectral theorem promotion
PVM construction
exact atom 33/20 derivation
positive spectral weight
physical Yang-Mills Hamiltonian promotion
```

---

## Audit and review entry points

Recommended external review order:

1. Run `bash scripts/check.sh` from a fresh clone.
2. Run `lake build`.
3. Read `THEOREM_INDEX.md`.
4. Read `EXTERNAL_AUDIT_PACKET.md`.
5. Read `INDEPENDENT_REPLAY.md`.
6. Inspect the physical normalization boundary in `PHYSICAL_REALIZATION_BOUNDARY.md`.
7. Inspect the R4 spectral-measure/PVM files listed above.
8. Verify that finite-supported local PVM is not promoted to genuine spectral measure.
9. Verify that actual-Borel carrier/wrapper closure is not promoted to operator-valued countable additivity.
10. Inspect the R2 local analytic lane only as a support/boundary lane.
11. Record review notes append-only.

Core commands and files:

| Entry point | Role |
|---|---|
| `bash scripts/check.sh` | Complete local replay path. |
| `lake build` | Lean kernel build gate for the configured roots. |
| `THEOREM_INDEX.md` | Theorem / bridge / target surface map. |
| `EXTERNAL_AUDIT_PACKET.md` | Top-level external review packet. |
| `INDEPENDENT_REPLAY.md` | Fresh-clone replay procedure. |
| `PHYSICAL_REALIZATION_BOUNDARY.md` | Boundary for physical interpretation. |
| `MGAP4D/R4/TheoremSurface.lean` | Current root-integrated R4 theorem surface. |
| `MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelEndpointCarrier.lean` | Actual Set ℝ endpoint carrier. |
| `MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelEndpointSetAlgebra.lean` | Endpoint Boolean set algebra. |
| `MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelSetWrapper.lean` | Actual Borel wrapper phase surface. |
| `MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelSetAlgebraClosure.lean` | Wrapper closure phase surface. |

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

The DOI-backed Zenodo record is a proof-architecture and external-audit preparation report. It does not by itself open public final theorem release.

---

## Contribution and review policy

External contributions are most useful when they improve one of the following:

```text
fresh-clone replay
Lean kernel checking
theorem-surface inspection
R4 actual-Borel carrier / wrapper review
operator-topology countable-additivity review
self-adjoint spectral theorem handoff review
physical-normalization review
continuum-Hamiltonian review
concrete l2 R2 support-lane review
audit-script precision
documentation consistency
external mathematical review
```

Do not treat documentation, CI ledgers, local finite-supported PVM scaffolds, or audit scripts as substitutes for Lean kernel checking and mathematical proof review.
