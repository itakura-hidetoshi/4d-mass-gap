# Actual finite Wilson → Osterwalder–Schrader physical excitation proof record

Status date: 2026-08-15 (JST)

Repository: `itakura-hidetoshi/4d-mass-gap`

Canonical branch: `formal/real-hilbert-uniform-coercive-strong-limit`

Working PR: #1670 — `Lift actual Wilson strictness to a reconstructed physical excitation`

Working branch: `formal/actual-wilson-os-physical-excitation-v1`

Exact PR base: `7fb099ddc94275f0b0832d98aefc25bc5a699196`

This document is the continuation record for the actual finite Wilson / Wightman–OS / physical-Hamiltonian route. It records what is mathematically proved, what is Lean-green, what has only been reduced to a smaller local obligation, and what must **not** be inferred from the current code.

---

## 1. Claim boundary and non-negotiable invariants

The development must preserve all previously frozen physical and mathematical statements. In particular, no continuation step may weaken:

- the theorem statements already routed to the final physical carrier;
- the physical assumptions;
- the exact target mass value `33/20`;
- the decay-rate route;
- finite coercivity `1/2`;
- the moving-time `o(a_n)` residual requirement;
- determinant requirements;
- projective coherence / same-root requirements;
- the existing OS/Wightman and spectral/PVM routing.

The current route also obeys the following negative claims:

- no new Hilbert carrier is introduced;
- the static finite Wilson Gram operator `A†A` is **not** identified with Euclidean time evolution;
- no global surjectivity of the coherent positive-half pullback is assumed;
- no abstract `Dense` hypothesis is to be introduced merely to discharge the current finite Wilson realization frontier;
- no new positivity, spectral, coercivity, determinant, decay, moving-time, or mass assumption is introduced by the actual-analysis bridge.

The intended proof architecture remains:

`generic Mathlib theorem → actual finite Wilson realization → OS positive-time carrier → completed physical Hilbert space → physical Hamiltonian / mass route`.

---

## 2. Current exact CI fixed points

### Last fully green fixed point

Commit:

```text
20a0c88b41388f6f5c8bcbb9b72afc594654e4b7
```

Fast Check:

```text
PR Lean Fast Check #10419
run id 31854143113
completed / success
Changed Lean fast check: completed / success
Run changed Lean fast check step: completed / success
```

At this fixed point, the action-level closure hypotheses have already been reduced to actual single-plaquette representatives.

### Subsequent experimental head

Commit:

```text
c45d7c071f6168ea867e079e2da1adde6df8e7c1
```

Commit message:

```text
Generate Gram closure from actual plaquette algebra
```

Fast Check:

```text
PR Lean Fast Check #10420
run id 31854390273
completed / failure
```

This failure is localized to:

```text
MGAP4D/MathlibAnalytic/
  PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure.lean
```

The run passed:

- changed-Lean preflight audit;
- source-integrity audit;
- forbidden-token audit (`sorry=0`, `admit=0`, `axiom=0`, `constant=0` in audited sources before elaboration);
- hard physical residual ledger audit;
- analytic bridge coherence audit;
- final physical carrier routing audit;
- OS/Wightman mass-gap proof-route audit.

The actual Lean failure is not a mathematical counterexample. The first errors are missing classical decidability for

```lean
periodicHypercubicEvenStrictPositivePlaquette p
```

and

```lean
periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p
```

inside `if`-defined `ContinuousMap`s, followed by `simp` goals downstream from those definitions. The previous file

```text
PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeaturePlaquetteGeneratorClosure.lean
```

built successfully in the same #10420 run.

Therefore `c45d7c...` is **not** a green proof fixed point. The last green proof fixed point remains `20a0c88...` until the local elaboration issue is repaired and a completed successful run is observed.

---

## 3. Actual-analysis object and the true analytic frontier

The explicit raw actual-analysis representative is, schematically,

\[
  g_{\mathrm{raw}}(x)
  =
  \int_{\partial}
    p(b)\,\psi_{\partial}(b)\,K(b,x)\,d\mu(b).
\]

Here:

- `b` is shared reflection-fixed boundary data;
- `p(b)` is the concrete normalized-trace polynomial boundary probe;
- `ψ_boundary(b)` is the actual finite Wilson OS boundary vacuum wavefunction / moment;
- `K(b,x)` is the completed-positive boundary Gram feature;
- `x` is the positive open-half configuration.

The L² bundling is **not** the current frontier. The repository already has the `ContinuousMap.toLp` handoff. Thus the relevant unresolved statement is a uniform / C⁰ closure statement of the form

\[
  g_{\mathrm{raw}}
  \in
  \overline{\mathcal C_{+,\mathrm{gauge}}}^{\|\cdot\|_\infty},
\]

or, more concretely in the current finite plaquette route,

\[
  g_{\mathrm{raw}}
  \in
  \overline{\mathcal A_{\mathrm{plaq}}}^{\|\cdot\|_\infty},
\]

for an actual positive-half Wilson/plaquette algebra that can then be lifted into the existing positive-time OS observable image.

Once this C⁰ closure is obtained, the already-built C⁰→L² bridge can transfer it to the completed open-half Haar L² carrier.

---

## 4. Raw actual-analysis continuity is already theorem-generated

Relevant source:

```text
MGAP4D/MathlibAnalytic/
  PeriodicHypercubicEvenBoundaryRawActualAnalysisContinuity.lean
```

The theorem

```lean
periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysis_continuous
```

proves continuity of the explicit raw representative using dominated continuity.

The proof ingredients already present in the repository include:

1. boundedness of the normalized-trace polynomial on compact boundary configuration space;
2. measurability of the actual completed-positive Gram feature;
3. nonnegativity and a uniform partition-function bound for the Gram feature;
4. integrability of the OS boundary vacuum moment with respect to boundary Haar measure;
5. continuity in the positive open-half variable for fixed boundary data;
6. `MeasureTheory.continuous_of_dominated`.

The integrand is explicitly

```lean
fun x b => (p b * psi b) * K b x
```

and the raw output is the scalar boundary integral of this finite Wilson object. No abstract existence replacement is used here.

---

## 5. Structure of the completed-positive kernel

The kernel / feature used by raw actual analysis is the actual finite Wilson object

```lean
periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
```

and is structurally a boundary scalar coefficient times the completed-positive Wilson amplitude:

\[
K(b,x)
=
\sqrt{c_{\partial}(b)}\,
W_{+}^{\mathrm{completed}}(b,x).
\]

The completed-positive amplitude contains both finite interaction sectors:

\[
W_{+}^{\mathrm{completed}}
=
\exp(-\beta S_{\mathrm{bulk}}^{+})
\exp(-\beta S_{\mathrm{temporal},\partial}^{+}).
\]

The action terms are finite sums of actual periodic SU(N) Wilson plaquette energies after boundary-fibered assembly. No interaction sector is discarded.

---

## 6. Mathlib polynomial-closure step: Gibbs exponentials need no Dense assumption

Green source:

```text
MGAP4D/MathlibAnalytic/
  PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeaturePolynomialClosure.lean
```

The central generic helper is the statement that if

```lean
f ∈ A
```

for a real subalgebra

```lean
A : Subalgebra ℝ C(X, ℝ)
```

on compact `X`, then

```lean
x ↦ Real.exp (-beta * f x)
```

belongs to `A.topologicalClosure`.

The proof uses Mathlib's

```lean
ContinuousMap.comp_attachBound_mem_closure
```

rather than an ad hoc Taylor-series construction or a global Stone–Weierstrass density assumption. The bounded compact range

\[
[-\|f\|,\|f\|]
\]

is attached and the one-variable exponential is uniformly approximated there by polynomials.

Consequently, once the two actual finite Wilson actions satisfy

\[
S_{\mathrm{bulk}}^{(b)}\in A,
\qquad
S_{\mathrm{temporal}}^{(b)}\in A,
\]

one obtains

\[
\exp(-\beta S_{\mathrm{bulk}}^{(b)})
\in\overline A,
\]

\[
\exp(-\beta S_{\mathrm{temporal}}^{(b)})
\in\overline A,
\]

and by multiplication in the closed subalgebra,

\[
W_{+}^{\mathrm{completed}}(b,\cdot)
\in\overline A.
\]

Finally the boundary coefficient

\[
\sqrt{c_{\partial}(b)}
\]

is independent of the open-half variable, so scalar closure yields

\[
K(b,\cdot)\in\overline A.
\]

This is an important closed layer: **the Gibbs exponential is no longer an analytic frontier**.

---

## 7. Action membership reduced to actual single-plaquette representatives

Green source introduced at commit `20a0c88...`:

```text
MGAP4D/MathlibAnalytic/
  PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeaturePlaquetteGeneratorClosure.lean
```

This layer removes the action-level assumptions as primitive obligations.

The actual positive bulk action has the finite form

\[
S_{\mathrm{bulk}}^{(b)}(x)
=
\sum_{p\in\mathcal P}
\mathbf 1_{p\in\mathcal P_{+}}
E_p(\operatorname{assemble}(b,x,1)),
\]

and the positive-boundary temporal action has the analogous finite sum

\[
S_{\mathrm{temporal}}^{(b)}(x)
=
\sum_{p\in\mathcal P}
\mathbf 1_{p\in\mathcal P_{\partial,+}^{\mathrm{time}}}
E_p(\operatorname{assemble}(b,x,1)).
\]

The theorem package says: if each selected single-plaquette term has a continuous representative in `A`, then `Subalgebra.sum_mem` reconstructs each full action in `A`. The polynomial-closure theorem from Section 6 then yields the completed-positive amplitude and Gram feature in `A.topologicalClosure`.

Thus the green mathematical frontier at `20a0c88...` is no longer

```text
prove the Gibbs exponential is approximable
```

and no longer

```text
assume the whole action belongs to the observable algebra
```

but instead

```text
identify the actual single-plaquette continuous generators with one concrete finite positive-half Wilson/plaquette algebra.
```

---

## 8. Boundary-independent actual plaquette algebra design

The next source, currently present but not yet green at `c45d7c...`, is

```text
MGAP4D/MathlibAnalytic/
  PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure.lean
```

Its intended common algebra is

\[
\mathcal A_{\mathrm{plaq}}
=
\operatorname{Alg}_{\mathbb R}
\left\{
 x\mapsto
 E_p(\operatorname{boundaryFiberedAssemble}(b,x,1))
 : b\in\partial,\ p\in\mathcal P
\right\}.
\]

Lean definition:

```lean
periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
```

implemented through

```lean
Algebra.adjoin ℝ (Set.range ...)
```

of the actual continuous single-plaquette maps.

The reason for ranging over **all** boundary data in the generator set is crucial: the resulting subalgebra is one common subalgebra of

```lean
C(OpenHalfConfiguration, ℝ)
```

and does not change when the boundary variable `b` is later integrated out in `g_raw`.

The intended proof chain inside this file is:

```text
actual plaquette continuous map
  ∈ Algebra.adjoin generators
        ↓
selected positive term = generator or 0
selected boundary-temporal term = generator or 0
        ↓
finite sum / Subalgebra.sum_mem
        ↓
S_bulk(b,·), S_temporal(b,·) ∈ A_plaq
        ↓
Mathlib polynomial closure
        ↓
completed positive amplitude ∈ closure A_plaq
        ↓
K(b,·) ∈ closure A_plaq
```

The #10420 failure is a local elaboration defect in the selected-term `if` definitions / simplification, not a failure of this mathematical argument.

Until a completed successful CI run is obtained, however, the final two theorems of this file must be treated as **intended / not yet green**, not as established repository facts.

---

## 9. Positive-half pullback range equality is already proved without global surjectivity

Green source:

```text
MGAP4D/MathlibAnalytic/
  PhysicalYangMillsWilsonSU2FinitePositiveHalfObservableRangeBridge.lean
```

The key equality is

\[
\operatorname{range}(\mathrm{finitePositiveHalfObservable})
=
\operatorname{range}(Q.\mathrm{positiveHalfPullback}\ n).
\]

The proof does **not** assume that

```lean
Q.positiveHalfPullback n
```

is surjective onto all bounded continuous open-half functions.

The forward direction constructs the preimage using the already-existing positive-time observable `Pn.toPositiveTime F` and

```lean
finitePositiveHalfObservable_eq_positiveHalfPullback
```

(or the corresponding namespaced theorem).

The reverse direction uses the canonical OS carrier ↔ positive-time submodule correspondence / surjectivity of the carrier-to-positive-time map, then applies the same equality. Thus the range equality is an equality between two already-constructed finite physical/OS images, not a claim about all of `C(X,ℝ)` or all bounded continuous functions.

This distinction must be preserved in future documentation and theorem statements.

---

## 10. Existing C⁰ → L² → reconstructed excitation pipeline

The repository already contains the downstream route needed after the C⁰ range-closure statement is established. Relevant PR #1670 files include:

```text
PhysicalYangMillsWilsonSU2RawActualAnalysisContinuousPullbackClosure.lean
PhysicalYangMillsWilsonSU2PositiveTimeSubmoduleRangeClosure.lean
PhysicalYangMillsWilsonSU2RawActualAnalysisPhysicalExcitation.lean
PhysicalYangMillsWilsonSU2RawActualAnalysisExcitationDomainWitness.lean
PhysicalYangMillsWilsonSU2RawActualAnalysisDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2RawActualAnalysisClosureDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2RawActualAnalysisRangeClosureDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2AnalysisImageDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2BoundaryApproximationDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2BoundaryRangeDerivedRayleighMass.lean
PhysicalYangMillsWilsonSU2ActualAnalysisStrictPhysicalExcitation.lean
```

These layers are designed so that an actual finite Wilson raw-analysis image in the closure of the physical positive-time range can be transferred through the already-existing completed OS construction, yielding a nonzero reconstructed vacuum-orthogonal excitation and then the existing Rayleigh/mass route.

The current work must therefore close the **actual realization / closure input**, not recreate a second Hilbert-space or spectral theory.

---

## 11. Why a generic Dense shortcut is the wrong next step

There is an older generic cylinder-density bridge admitting a hypothesis such as

```lean
Dense carrier
```

for a chosen bounded-continuous carrier. That theorem is a valid generic implication, but it is **not** the desired final discharge of the actual finite Wilson frontier.

The current proof should instead descend to the actual finite ingredients:

- finite plaquette holonomies;
- actual SU(2) Wilson plaquette energies;
- finite positive bulk action;
- finite positive-boundary temporal action;
- exponential Gibbs weights;
- completed-positive Gram feature;
- actual positive-time/cylinder/Wilson observable carrier.

The purpose of Sections 6–8 is precisely to avoid replacing this concrete finite construction with an unproved global density assumption.

---

## 12. Next analytic step: upgrade the boundary integral to a C(X,ℝ)-valued Bochner integral

After the common plaquette-algebra file is green, the next target is to pass from the fixed-boundary theorem

\[
K(b,\cdot)\in\overline{\mathcal A_{\mathrm{plaq}}}
\quad\forall b
\]

to the raw integral

\[
g_{\mathrm{raw}}\in\overline{\mathcal A_{\mathrm{plaq}}}.
\]

The clean Mathlib route is to regard

\[
b\longmapsto
p(b)\psi_{\partial}(b)K(b,\cdot)
\]

as a Banach-space-valued function with values in

```lean
C(OpenHalfConfiguration, ℝ)
```

and identify its Bochner integral with the already-defined pointwise raw actual-analysis `ContinuousMap`.

To do this cleanly, the existing fixed-boundary continuity theorem

```lean
FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_continuous_positive
```

should be strengthened to joint continuity of

\[
(b,x)\longmapsto
\operatorname{boundaryFiberedAssemble}(b,x,1).
\]

The existing proof is coordinatewise and should extend directly: on a positive edge evaluate the open-half coordinate, on a fixed edge evaluate the boundary coordinate, and on a negative edge the chosen negative-half section is constant.

Joint continuity then permits continuous dependence

\[
b\mapsto K(b,\cdot)
\]

in the sup norm, making the Banach-valued integration route natural.

The desired endpoint of this step is

\[
\boxed{
 g_{\mathrm{raw}}
 \in
 \overline{\mathcal A_{\mathrm{plaq}}}^{\|\cdot\|_\infty}
}.
\]

---

## 13. Next algebraic/physical step: lift actual plaquette generators into the finite positive-half OS image

Even after the raw C⁰ closure in `A_plaq` is proved, one more concrete identification is required:

\[
\mathcal A_{\mathrm{plaq}}
\subseteq
\operatorname{range}(\mathrm{finitePositiveHalfObservable}).
\]

Together with the already-green equality

\[
\operatorname{range}(\mathrm{finitePositiveHalfObservable})
=
\operatorname{range}(Q.\mathrm{positiveHalfPullback}\ n),
\]

this yields

\[
g_{\mathrm{raw}}
\in
\overline{\operatorname{range}(Q.\mathrm{positiveHalfPullback}\ n)}.
\]

The lift should be proved generator-by-generator from actual finite Wilson/cylinder observables. It must not be replaced by global surjectivity.

The ideal chain is:

```text
single actual plaquette Wilson/energy observable
        ↓ actual positive-time cylinder/Wilson carrier
finite positive-half observable
        ↓ algebra operations
A_plaq ⊆ range(finitePositiveHalfObservable)
        ↓ existing range equality
A_plaq ⊆ range(Q.positiveHalfPullback n)
        ↓ closure monotonicity
raw actual-analysis ∈ closure(range(Q.positiveHalfPullback n))
        ↓ existing C⁰→L² bridge
raw Haar-L² output ∈ closure(range(positiveTimeSubmoduleL2LinearMap n))
        ↓ existing reconstructed-excitation theorem
nonzero vacuum-orthogonal physical excitation
        ↓ existing Rayleigh / mass route
physical mass conclusion
```

---

## 14. Exact current frontier

At the time of this record the frontier is:

### Green / closed

- actual raw-analysis continuity;
- `ContinuousMap.toLp` downstream L² bundling;
- completed-positive kernel continuity for fixed boundary;
- polynomial approximation of `exp(-β f)` in subalgebra closure using Mathlib;
- completed-positive amplitude closure from action membership;
- Gram-feature closure from action membership;
- reduction of action membership to actual single-plaquette representatives;
- finite-positive-half observable range equality with `Q.positiveHalfPullback n` without global pullback surjectivity;
- downstream C⁰→L² / reconstructed-excitation / Rayleigh bridge layers, conditional on the actual range-closure input.

### Implemented but not green

- one boundary-independent `Algebra.adjoin` generated by all boundary-fibered single-plaquette continuous maps;
- direct elimination of all single-plaquette representative hypotheses via `Algebra.subset_adjoin`;
- automatic `K(b,·) ∈ closure A_plaq` theorem.

Current blocker here is only the local classical-decidability / simplification elaboration failure in #10420.

### Not yet implemented / true remaining proof work

1. repair and green the actual `A_plaq` file;
2. prove joint continuity in `(b,x)` of boundary-fibered assembly and hence of the kernel family as needed for `C(X,ℝ)`-valued integration;
3. prove the raw boundary Bochner integral lies in the closed common plaquette algebra and equals the existing raw `ContinuousMap`;
4. prove actual plaquette/Wilson generators lift into the finite positive-half OS image;
5. use the green range equality to obtain the required positive-half pullback range closure;
6. invoke the existing C⁰→L² and physical-excitation pipeline;
7. continue the already-existing physical/exact-mass handoff without weakening the exact `33/20` target or any frozen quantitative assumption.

---

## 15. CI interpretation rule for this proof record

Only completed GitHub Actions evidence is authoritative.

- `queued` and `in_progress` are not success or failure evidence;
- when CI is running for the working branch/head, do not add another commit to that branch;
- distinguish Lean/code failure from cache, Actions, or external-infrastructure failure;
- only a completed successful final-head run can define a new green fixed point.

For PR #1670 specifically:

- `20a0c88b41388f6f5c8bcbb9b72afc594654e4b7` + Fast Check #10419 is the last completed-success fixed point recorded here;
- `c45d7c071f6168ea867e079e2da1adde6df8e7c1` + Fast Check #10420 is a completed Lean failure localized to `PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure.lean`.

---

## 16. Repository operation rules for continuation

For this proof line:

- use the GitHub connector for GitHub operations;
- do not use `gh` CLI or `git` CLI for repository mutation;
- normal PRs begin Draft from the exact canonical SHA;
- do not commit into a branch while its CI is running;
- do not auto-merge;
- merge by squash only;
- when merging, fix `expected_head_sha`;
- before Ready and again after Ready, audit final head, completed CI, base SHA, mergeability, reviews, unresolved inline threads, and sibling open/Draft PRs.

PR #1670 must remain Draft until the actual realization condition is theorem-generated through the existing finite Wilson/projective/OS route and the downstream physical handoff is genuinely closed.

---

## 17. Compact continuation checkpoint

A future continuation should begin with the following facts:

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Canonical branch:
  formal/real-hilbert-uniform-coercive-strong-limit

PR:
  #1670

Working branch:
  formal/actual-wilson-os-physical-excitation-v1

Exact base:
  7fb099ddc94275f0b0832d98aefc25bc5a699196

Last green head:
  20a0c88b41388f6f5c8bcbb9b72afc594654e4b7

Green CI:
  Fast Check #10419
  completed / success

Next experimental source head before this documentation commit:
  c45d7c071f6168ea867e079e2da1adde6df8e7c1

Its CI:
  Fast Check #10420
  completed / failure

Exact code failure:
  PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure.lean
  missing Decidable/classical elaboration for the two plaquette-selection Props,
  followed by simp goals in selected-term apply/membership lemmas.

Mathematical frontier:
  fixed-b K(b,·) C⁰ closure via actual plaquette algebra
  → boundary Bochner integration in C(X,ℝ)
  → actual plaquette generator lift into finitePositiveHalfObservable range
  → range(Q.positiveHalfPullback n) closure
  → existing C⁰→L² bridge
  → reconstructed nonzero vacuum-orthogonal excitation
  → existing physical Rayleigh/mass route.
```

This checkpoint intentionally distinguishes theorem-generated facts from intended but non-green code, so that later work does not accidentally promote a local elaboration attempt into a proved mathematical statement.
