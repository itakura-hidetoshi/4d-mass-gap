# Actual Wilson → OS physical excitation: green-status addendum

Status date: 2026-08-15 (JST)

Repository: `itakura-hidetoshi/4d-mass-gap`

PR: #1670 — `Lift actual Wilson strictness to a reconstructed physical excitation`

Working branch: `formal/actual-wilson-os-physical-excitation-v1`

Canonical PR base: `7fb099ddc94275f0b0832d98aefc25bc5a699196`

This addendum updates only the **verification status** of the detailed records below. It does not replace their mathematical content:

- `docs/actual_wilson_os_physical_excitation_proof_record_2026-08-15.md`
- `docs/actual_wilson_c0_closure_frontier_2026-08-15.md`

Those two documents were intentionally written while the newest actual-plaquette-algebra layer was not yet green. Their descriptions of the #10420 failure are retained as historical audit evidence. The status statements saying that `20a0c88...` was the last green fixed point are superseded by this addendum.

---

## 1. New verified fixed point

The validated parent head for this addendum is:

```text
5927c30b4afa67cc2bb9e2846b8a128b22c04cbc
```

It contains, as ancestors, the local elaboration repair:

```text
3d947cad5f3881ebf926b93e848d3a04990fc872
Fix classical plaquette sector selection elaboration
```

and the two proof-record documentation commits:

```text
87ed0f303cbbf538f74b8265e2d906d19d35d93b
Record actual Wilson OS physical excitation proof frontier

5927c30b4afa67cc2bb9e2846b8a128b22c04cbc
Document actual Wilson C0 closure proof frontier
```

Completed CI evidence for `5927c30...`:

```text
PR Lean Fast Check #10423
run id: 31855024865
status: completed
conclusion: success

job: Changed Lean fast check
status: completed
conclusion: success

step: Run changed Lean fast check
status: completed
conclusion: success
```

Therefore the repaired actual-plaquette-algebra package is now Lean-green. The previous green fixed point `20a0c88...` is no longer the latest verified frontier.

---

## 2. Exact interpretation of the #10420 → #10423 sequence

The relevant chronology is:

```text
20a0c88b41388f6f5c8bcbb9b72afc594654e4b7
  Fast Check #10419: completed / success
  finite action membership reduced to actual single-plaquette representatives

c45d7c071f6168ea867e079e2da1adde6df8e7c1
  Fast Check #10420: completed / failure
  failure localized to classical Decidable elaboration in
  PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure.lean

3d947cad5f3881ebf926b93e848d3a04990fc872
  local repair only:
  proposition-selected ContinuousMap definitions now enter a `classical` block
  no theorem statement or mathematical assumption changed

Fast Check #10421 on 3d947cad...
  completed / cancelled
  not used as success or failure evidence

87ed0f303cbbf538f74b8265e2d906d19d35d93b
  first documentation commit
  Fast Check #10422: completed / cancelled
  not used as success or failure evidence

5927c30b4afa67cc2bb9e2846b8a128b22c04cbc
  second documentation commit
  Fast Check #10423: completed / success
  validates the repaired Lean ancestry and both documentation files
```

The cancelled runs are deliberately not promoted to evidence. Only #10423 establishes the current green status.

---

## 3. What is now theorem-generated and green

The following finite C⁰ chain is now verified through the actual common plaquette algebra layer.

For a fixed positive open-half configuration space `X`, define the actual boundary-fibered single-plaquette continuous function

```text
x ↦ specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy
        (boundaryFiberedAssemble b x 1) p)
```

bundled in Lean as

```lean
periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap
```

and define the common actual plaquette algebra

```lean
periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
```

by

```lean
Algebra.adjoin ℝ
  (Set.range fun (b,p) =>
    periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap ... b p)
```

where the generator family ranges over **all boundary configurations and all plaquettes**. Hence the ambient algebra is independent of the boundary parameter that will later be integrated out.

The green proof now establishes:

```text
actual single-plaquette energy
  ∈ A_plaq

strict-positive selected plaquette term
  ∈ A_plaq

positive-boundary-temporal selected plaquette term
  ∈ A_plaq

finite sums
  ⇒ positive bulk Wilson action ∈ A_plaq
  ⇒ positive-boundary-temporal Wilson action ∈ A_plaq
```

The already-green Mathlib polynomial-closure layer then gives

```text
exp (-β S_bulk) ∈ closure A_plaq
exp (-β S_temporal) ∈ closure A_plaq
```

using

```lean
ContinuousMap.comp_attachBound_mem_closure
```

on the compact range of each action, not an abstract global density assumption.

Closure under multiplication gives the completed positive Wilson amplitude in `A_plaq.topologicalClosure`, and scalar closure by the boundary Gram coefficient gives

```text
K(b,·) ∈ A_plaq.topologicalClosure
```

for every fixed boundary configuration `b`.

The corresponding final theorem is:

```lean
periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMap_mem_actualPlaquetteAlgebra_topologicalClosure
```

in

```text
MGAP4D/MathlibAnalytic/
  PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure.lean
```

This theorem is now green under Fast Check #10423.

---

## 4. What this new green result removes

The following are no longer unresolved obligations in this route:

1. **Gibbs exponential approximation.**
   It is handled by Mathlib compact-range polynomial approximation.

2. **Whole-action membership assumptions `hBulk` / `hTemporal`.**
   They have been reduced and then discharged from actual finite plaquette generators and finite sums.

3. **Boundary-dependent choice of observable algebra.**
   One common algebra generated over all boundary data is now defined, so all fixed-boundary kernels land in the closure of the same ambient algebra.

4. **The local `Decidable` elaboration failure from #10420.**
   It was a classical proposition-selection issue only and is repaired without changing mathematics.

---

## 5. What remains unproved: exact C⁰ frontier

The full raw actual-analysis representative is

\[
  g_{\mathrm{raw}}(x)
  =
  \int_{\partial}
    p(b)\,\psi_{\partial}(b)\,K(b,x)\,d\mu(b).
\]

The fixed-boundary result

\[
  K(b,\cdot)\in\overline{\mathcal A_{\mathrm{plaq}}}
\]

is now green, but the boundary integral has **not yet** been proved to remain in that same C⁰ closure.

The next analytic target is therefore to bundle

\[
  \Phi(b)
  =
  p(b)\,\psi_{\partial}(b)\,K(b,\cdot)
  \in C(X,\mathbb R)
\]

and prove that its Bochner integral is the existing raw `ContinuousMap` and lies in the closed subspace/algebra closure.

A clean additive route is:

1. prove joint continuity of

   ```text
   (b,x) ↦ boundaryFiberedAssemble b x 1;
   ```

2. propagate joint continuity through actual plaquette holonomy, Wilson energy, finite actions, exponentials and the completed Gram feature;
3. use the compact-domain continuous-map exponential law to obtain sup-norm continuity of

   ```text
   b ↦ K(b,·) : C(X,ℝ);
   ```

4. prove Bochner integrability of

   ```text
   b ↦ (p b * psi_boundary b) • K(b,·);
   ```

5. prove the Bochner integral remains in

   ```text
   (periodicHypercubicEvenBoundaryActualPlaquetteAlgebra ...).topologicalClosure;
   ```

6. identify that `C(X,ℝ)`-valued integral pointwise with the already-established scalar raw actual-analysis representative.

This should yield

\[
  g_{\mathrm{raw}}
  \in
  \overline{\mathcal A_{\mathrm{plaq}}}^{\|\cdot\|_\infty}.
\]

---

## 6. The finite-to-physical lift remains a separate obligation

Even after the raw C⁰ integral is placed in `closure A_plaq`, one must still prove that the relevant actual plaquette generators/approximants are genuine theorem-generated positive-time finite Wilson observables.

The required direction is an actual realization theorem of the form

\[
  \mathcal A_{\mathrm{plaq}}
  \subseteq
  \operatorname{range}(\mathrm{finitePositiveHalfObservable})
\]

or a sufficiently strong corresponding inclusion of the approximating carrier.

The already-green theorem

\[
\operatorname{range}(\mathrm{finitePositiveHalfObservable})
=
\operatorname{range}(Q.\mathrm{positiveHalfPullback}\,n)
\]

then converts that actual finite realization into the physical positive-time pullback range.

This equality is **not** global surjectivity of `Q.positiveHalfPullback` onto all bounded-continuous open-half functions. It only identifies two already-constructed finite/OS images.

Before using the universal all-boundary plaquette algebra as a physical carrier, one must verify gauge invariance and actual positive-time/cylinder realizability of its generators. This is an explicit remaining theorem obligation and must not be silently inferred from the `Algebra.adjoin` definition.

---

## 7. Downstream route already available once C⁰ realization is closed

After proving

\[
  g_{\mathrm{raw}}
  \in
  \overline{\operatorname{range}(Q.\mathrm{positiveHalfPullback}\,n)}^{C^0},
\]

the repository already has the downstream chain:

```text
C⁰ / bounded-continuous range closure
  ↓ BoundedContinuousFunction.toLp
open-half Haar L² range closure
  ↓ Mathlib sequential closure
nonzero reconstructed OS vacuum-orthogonal excitation
  ↓ existing self-adjoint Hamiltonian domain machinery
PhysicalYangMillsExcitationDomainWitness
  ↓ Rayleigh variational definition
0 ≤ physicalYangMillsMass
```

Relevant files include:

```text
PhysicalYangMillsWilsonSU2RawActualAnalysisContinuousPullbackClosure.lean
PhysicalYangMillsWilsonSU2PositiveTimeSubmoduleRangeClosure.lean
PhysicalYangMillsWilsonSU2RawActualAnalysisRangeClosureDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2RawActualAnalysisPhysicalExcitation.lean
PhysicalYangMillsWilsonSU2RawActualAnalysisExcitationDomainWitness.lean
PhysicalYangMillsWilsonSU2RawActualAnalysisDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2ActualAnalysisStrictPhysicalExcitation.lean
PhysicalYangMillsWilsonSU2ActualAnalysisExcitationDomainWitness.lean
PhysicalYangMillsWilsonSU2AnalysisImageDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2BoundaryRangeDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2BoundaryApproximationDerivedRayleighMass.lean
```

The exact Riesz–Fubini identification already proved in

```text
PeriodicHypercubicEvenWilsonBoundaryAnalysisApplyRawActualAnalysis.lean
```

identifies the canonical Hilbert–Schmidt analysis operator output on the normalized-trace mode with the explicit raw actual-analysis Haar L² vector. Thus no duplicate raw-range premise is needed once the canonical analysis image is realized.

---

## 8. Claim discipline remains unchanged

This green status does **not** mean that PR #1670 completes the full Yang–Mills existence and mass-gap theorem.

In particular, this addendum does not assert:

- a global density theorem for all continuous open-half functions;
- global surjectivity of the positive-half pullback;
- that the universal actual plaquette algebra is already proved to lie in the physical positive-time image;
- that the boundary Bochner integral closure has already been discharged;
- that the static Wilson Gram operator `A†A` is Euclidean time translation;
- a new numerical mass theorem in this PR.

The exact mass target `33/20`, decay route, finite coercivity `1/2`, moving-time `o(a_n)` residual, determinant, projective coherence and same-root requirements remain frozen and unchanged.

PR #1670 remains Draft until the remaining actual finite realization/closure handoff and downstream physical/exact-mass route are genuinely closed.

---

## 9. Current continuation checkpoint

The safe continuation checkpoint after Fast Check #10423 is:

```text
validated proof/docs parent head:
  5927c30b4afa67cc2bb9e2846b8a128b22c04cbc

completed CI:
  PR Lean Fast Check #10423
  run id 31855024865
  completed / success

newly green mathematical statement:
  for every fixed boundary b,
  K(b,·) ∈ closure(A_plaq)
  with A_plaq generated by actual boundary-fibered single-plaquette Wilson energies

next hard residuals:
  (1) joint boundary/open-half continuity and C(X,ℝ)-valued Bochner integration;
  (2) actual plaquette/cylinder generators → theorem-generated finite positive-half observable image;
  (3) then existing C⁰→L²→physical excitation→Rayleigh/mass pipeline.
```

The detailed proof record and the C⁰ frontier note should be read together with this addendum; where their CI-status language reflects the earlier #10420 failure, this addendum is the authoritative later verification status.