# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
Authoritative proof carrier: formal/real-hilbert-uniform-coercive-strong-limit
Development roadmap: ROADMAP.md
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Authoritative development status — 2026-07-10 JST

The authoritative proof carrier is:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest integrated theorem checkpoint is:

```text
PR #746 — Identify direct bounded exact first excitation
PR head a38aea205dce9fe07b949c2e1b34cb3a160ac927
merge commit f300370b08736240342cb05885e6ffa7a174ed1b
PR Lean Fast Check run 5807 — success
post-merge carrier comparison — identical
```

The active carrier has advanced beyond the direct bounded operator handoff and the first complete-construction certificate.

It now contains a theorem and certificate chain that, for a supplied
`EuclideanYangMillsContinuumMeasureConstructionSpine`, identifies the exact lower spectral structure of the reconstructed model.

## Current formal result

Every theorem in the current exact-gap layer is parametrized by:

```lean
S : EuclideanYangMillsContinuumMeasureConstructionSpine
```

Write:

```lean
σ := S.definitionBridge.spine.model.energySpectrum
Δ := exactGapValueReal
E₁ := S.definitionBridge.spine.model.firstExcitation
```

The integrated carrier proves the following consequences:

```lean
HasHamiltonianMassGap σ Δ

σ ⊆ ({0} : Set ℝ) ∪ Set.Ici Δ

Set.Ioo 0 Δ ∩ σ = ∅

Δ ∈ σ

IsLeast (σ \ ({0} : Set ℝ)) Δ

sInf (σ \ ({0} : Set ℝ)) = Δ

σ ∩ Set.Iio Δ = ({0} : Set ℝ)

(σ \ ({0} : Set ℝ)) ∩ Set.Iic Δ = ({Δ} : Set ℝ)

σ ∩ Set.Iic Δ = ({0, Δ} : Set ℝ)

E₁ = Δ

IsLeast (σ \ ({0} : Set ℝ)) E₁

∃! E : ℝ, IsLeast (σ \ ({0} : Set ℝ)) E

∃ ψ : S.definitionBridge.spine.model.H,
  ψ ∈ S.definitionBridge.spine.model.spectralPVM ({Δ} : Set ℝ)
```

Thus, inside the supplied construction spine, the exact gap is attained, is the unique least nonzero spectral energy, equals the model first excitation, and separates the vacuum from the remaining spectrum.

These statements are formal Lean theorems on the active carrier.

They do not by themselves construct the required construction spine from a concrete four-dimensional Yang--Mills approximation family.

## Primary exact-spectrum surfaces

The current certificate chain is:

```lean
EuclideanYangMillsCompleteConstructionDirectBoundedCertificate

EuclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate

EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate

EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate
```

The principal compact theorem endpoints are:

```lean
euclidean_yang_mills_complete_construction_direct_bounded_package

euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificate_complete

euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparation_complete

euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitation_complete
```

The latest files are:

```text
MGAP4D/MathlibAnalytic/EuclideanYangMillsCompleteConstructionDirectBoundedExactGapInterval.lean
MGAP4D/MathlibAnalytic/EuclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate.lean
MGAP4D/MathlibAnalytic/EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparation.lean
MGAP4D/MathlibAnalytic/EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate.lean
MGAP4D/MathlibAnalytic/EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitation.lean
MGAP4D/MathlibAnalytic/EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate.lean
```

## Direct bounded public route

The preferred boundedness surface remains the direct bare-`M` bundle.

```lean
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package
```

Route-backed boundedness names remain compatibility surfaces.

The direct route is exposed through root, downstream, public-consumer, and compact root-consumer APIs integrated by PRs #721 through #743.

Those layers reduce repeated destructuring and provide stable theorem-facing imports.

They do not add new physical hypotheses or independently construct a spectral measure.

## Exact-gap normalization

`exactGapValueReal` is the public projection of the Hamiltonian/PVM/spectral exact-gap package.

It is not defined in `ExactGapReal.lean` by a free-standing real literal.

The exact `33/20` statement belongs to its upstream provenance route.

That normalization route is not, by itself, an unconditional derivation of a physical four-dimensional Yang--Mills mass scale.

## Integrated proof route

```text
finite Wilson and heat-bath theorem generators
  -> conditional continuum, OS, Hamiltonian, resolvent, and graph-limit packages
  -> exact-gap normalization and provenance route
  -> R4 continuum-measure construction spine
  -> gauge-field, gauge-action, gauge-invariant, Schwinger, and correlation layers
  -> reflection-positive reconstruction input
  -> quotient, section, range, and transport layers
  -> standard real Hilbert completion
  -> completed Hilbert-space handoff
  -> completed OS semigroup handoff
  -> generator and Hamiltonian handoffs
  -> mathlib self-adjoint LinearPMap operator
  -> graph, adjoint, actual-operator, and continuous-representative packages
  -> direct bare-M bounded operator bundle
  -> complete-construction direct bounded certificate
  -> downstream and public-consumer API chain
  -> positive nonzero-spectrum and lower-bound packages
  -> exact-gap interval certificate
  -> exact-threshold spectral classification
  -> exact first-excitation identification
  -> physical construction-spine instantiation
  -> independent review and final theorem assessment
```

## The theorem boundary

| Surface | Status on the active carrier |
|---|---|
| Finite Wilson and finite heat-bath theorem generators | available |
| Conditional continuum, OS, Hamiltonian, resolvent, graph-limit, and spectral interfaces | available as theorem packages |
| R4 reconstruction through completed Hilbert space | integrated |
| OS semigroup, generator, Hamiltonian, and self-adjoint operator APIs | integrated |
| Direct bare-`M` bounded operator route | integrated through PR #717 |
| Complete-construction direct bounded certificate | integrated through PR #718 |
| Stable downstream and public-consumer route | integrated through PR #743 |
| Positive nonzero-spectrum and lower-bound certificate packages | integrated through PR #739 |
| Exact-gap interval and attained least nonzero energy | integrated by PR #744 |
| Exact lower-threshold spectral classification | integrated by PR #745 |
| First excitation equals the exact gap and is uniquely least | integrated by PR #746 |
| Concrete physical construction of `EuclideanYangMillsContinuumMeasureConstructionSpine` | open |
| Discharge of all continuum, nontriviality, spectral, and gap data from one specified physical family | open |
| Unconditional four-dimensional Yang--Mills existence and mass-gap theorem | not claimed |
| Independent external mathematical consensus | not claimed |

## What remains open

The decisive frontier is no longer the packaging of the direct bounded route or the derivation of elementary order consequences from an already supplied spectral package.

The decisive frontier is to construct the required `EuclideanYangMillsContinuumMeasureConstructionSpine` from one concrete physical approximation family and prove that the family supplies every field used by the exact-gap theorem chain.

This includes:

```text
specifying the gauge group, lattice or regularization family, boundary conditions, and observables;
proving tightness or compactness and existence of the continuum limit;
proving nontriviality and the required Euclidean, gauge, and reflection-positive properties;
constructing the physical Hilbert space and Hamiltonian from that family;
deriving the spectral/PVM and exact-gap inputs from the physical construction rather than supplying them through the spine;
showing that the resulting theorem has the intended physical normalization and scope;
obtaining independent mathematical review.
```

Until those steps are discharged, the latest exact-spectrum theorems remain construction-spine-parametrized results rather than an unconditional Clay Millennium solution.

## Replay

Pinned Lean toolchain:

```text
leanprover/lean4:v4.30.0-rc2
```

Pinned mathlib revision:

```text
5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

From a fresh clone:

```bash
lake update
lake build
```

The repository also runs a focused PR Lean Fast Check for each theorem layer.

Before treating a result as integrated, verify the PR base, fixed head SHA, successful check, merge commit, and post-merge comparison against the active carrier.

## Development discipline

The active workflow is:

```text
create one focused branch from the current proof carrier;
open a Draft PR;
run PR Lean Fast Check;
mark ready only after the fixed head succeeds;
merge into formal/real-hilbert-uniform-coercive-strong-limit;
verify the merge commit is identical to the carrier head;
start the next theorem layer from the updated carrier.
```

Open, stale, superseded, closed-unmerged, or failing PRs are not active-carrier facts.

The default `main` branch is a repository landing surface.

Authoritative theorem integration status is determined by the active proof carrier named above.
