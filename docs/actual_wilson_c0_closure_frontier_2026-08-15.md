# Actual Wilson C⁰ closure frontier

Date: 2026-08-15 (JST)

Repository: `itakura-hidetoshi/4d-mass-gap`

PR: #1670 — `Lift actual Wilson strictness to a reconstructed physical excitation`

Branch: `formal/actual-wilson-os-physical-excitation-v1`

Canonical base of the PR: `7fb099ddc94275f0b0832d98aefc25bc5a699196`

## Status boundary

This note records the current finite-Wilson / Osterwalder–Schrader realization frontier. It deliberately distinguishes theorem-generated green results from the newest, not-yet-green implementation.

Last fully green proof head before the newest actual-plaquette-algebra package:

- head: `20a0c88b41388f6f5c8bcbb9b72afc594654e4b7`
- PR Lean Fast Check: #10419
- result: `completed / success`

Newest implementation head at the time of this note:

- head before this documentation commit: `c45d7c071f6168ea867e079e2da1adde6df8e7c1`
- PR Lean Fast Check: #10420
- result: `completed / failure`
- failure is a Lean elaboration failure in `PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure.lean`, not an Actions/cache/external-infrastructure failure.

No theorem statement, physical assumption, exact mass value `33/20`, finite coercivity `1/2`, decay rate, moving-time `o(a_n)` residual, determinant requirement, or projective-coherence requirement is weakened by this work.

## 1. The actual frontier is C⁰, not L²

The explicit raw finite Wilson actual-analysis representative has the form

\[
 g_{\rm raw}(x)
 =
 \int_{\partial}
 p(b)\,\psi_{\partial}(b)\,K(b,x)\,d\mu(b).
\]

Here:

- `b` is the reflection-fixed boundary configuration,
- `x` is the positive open-half configuration,
- `p(b)` is the chosen normalized-trace polynomial boundary probe,
- `psi_boundary(b)` is the finite Wilson OS boundary vacuum wavefunction,
- `K(b,x)` is the completed-positive Gram feature.

Continuity of this raw representative is already proved in

`PeriodicHypercubicEvenBoundaryRawActualAnalysisContinuity.lean`.

The L² bundling downstream is already handled by Mathlib's `ContinuousMap.toLp` layer. Therefore the remaining realization problem is not an L² construction problem. The genuine frontier is the sup-norm statement

\[
 g_{\rm raw}
 \in
 \overline{\mathcal C_{+,\mathrm{gauge}}}^{\|\cdot\|_\infty},
\]

for the actual positive-time finite Wilson/cylinder/plaquette observable algebra.

Once this C⁰ closure statement is available, the existing C⁰→L² bridge transfers it to the closure of the positive-time L² realization, and the already-built reconstructed-excitation machinery applies.

## 2. The coherent pullback range bridge is already theorem-generated

`PhysicalYangMillsWilsonSU2FinitePositiveHalfObservableRangeBridge.lean` proves that the range of the theorem-generated finite positive-half observable is exactly the range of the coherent physical positive-time pullback:

\[
 \operatorname{range}(\mathrm{finitePositiveHalfObservable})
 =
 \operatorname{range}(Q.\mathrm{positiveHalfPullback}\,n).
\]

This is **not** an assumption of global surjectivity of `Q.positiveHalfPullback` onto all bounded continuous open-half functions.

The reverse inclusion is obtained from the canonical OS-carrier ↔ positive-time-observable correspondence and the identity

```lean
finitePositiveHalfObservable_eq_positiveHalfPullback
```

by constructing actual preimages inside the existing OS carrier.

Therefore the remaining C⁰ task should target the actual finite observable algebra and then use this range equality. A separate abstract `Dense` hypothesis on the whole continuous function space is neither necessary nor desired.

## 3. Gibbs exponentials are no longer the analytic obstruction

The file

`PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeaturePolynomialClosure.lean`

bundles the actual positive bulk and positive boundary-temporal Wilson actions as continuous maps on a fixed positive open-half fiber.

The key Mathlib theorem is

```lean
ContinuousMap.comp_attachBound_mem_closure
```

For a compact configuration space `X`, a real subalgebra

```lean
A : Subalgebra ℝ C(X, ℝ)
```

and `f ∈ A`, this gives polynomial approximation on the compact range of `f`. Applied to

\[
 t \mapsto e^{-\beta t},
\]

it yields

\[
 f\in A
 \Longrightarrow
 e^{-\beta f}
 \in
 \overline A.
\]

This avoids a custom Taylor-series proof and avoids introducing a global Stone–Weierstrass density assumption.

For the actual finite Wilson positive half, if

\[
 S_{\rm bulk}^{(b)}\in A,
 \qquad
 S_{\rm temporal}^{(b)}\in A,
\]

then

\[
 e^{-\beta S_{\rm bulk}^{(b)}}\in\overline A,
 \qquad
 e^{-\beta S_{\rm temporal}^{(b)}}\in\overline A.
\]

Since `A.topologicalClosure` is again a subalgebra, multiplication gives the completed positive Wilson amplitude in `A.topologicalClosure`. Scalar multiplication by the boundary-dependent factor

\[
 \sqrt{\mathrm{boundaryCompletedPositiveGramCoefficient}(b)}
\]

then gives

\[
 K(b,\cdot)\in\overline A.
\]

Thus the exponential Gibbs factor itself is no longer the hard residual.

## 4. Action membership was reduced to actual single-plaquette generators

The green commit

`20a0c88b41388f6f5c8bcbb9b72afc594654e4b7`

adds

`PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeaturePlaquetteGeneratorClosure.lean`.

Its purpose is to remove the action-level assumptions

```lean
hBulk : positiveBulkActionContinuousMap ... ∈ A
hTemporal : positiveBoundaryTemporalActionContinuousMap ... ∈ A
```

and replace them by local single-plaquette representatives.

Both finite Wilson actions are literally finite sums of proposition-selected plaquette energies:

\[
S_{\rm bulk}
 = \sum_p
   1_{\{p\text{ strict positive}\}}\,E_p,
\]

and

\[
S_{\rm temporal}
 = \sum_p
   1_{\{p\text{ positive-boundary temporal}\}}\,E_p.
\]

Therefore, once each selected term has a continuous representative in one common subalgebra `A`, `Subalgebra.sum_mem` / finite-sum closure reconstructs both actions. The polynomial-closure theorem then immediately produces the completed-positive Gram feature closure.

This package passed Fast Check #10419.

## 5. Intended common actual plaquette algebra

The newest package

`PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure.lean`

implements the next, stronger construction.

The intended common algebra is

\[
\mathcal A_{\rm plaq}
=
\operatorname{Alg}_{\mathbb R}
\left\{
 x\mapsto
 E_p\bigl(\operatorname{boundaryFiberedAssemble}(b,x,1)\bigr)
 : b\in\partial,\ p\in\mathcal P
\right\}.
\]

In Lean this is naturally expressed with `Algebra.adjoin` over the set/range of the actual boundary-fibered plaquette-energy `ContinuousMap`s.

The important design point is that **the algebra itself is independent of a fixed boundary `b`**. Its generating family ranges over all boundary data and all plaquettes. This is necessary for the later boundary integral: all kernels `K(b,·)` must live in the closure of one common subalgebra.

The desired proof chain is

\[
\begin{aligned}
&\text{single actual plaquette energy}
  \in \mathcal A_{\rm plaq}
\\
&\Downarrow
\\
&\text{strict-positive selected term},\
  \text{positive-boundary-temporal selected term}
  \in \mathcal A_{\rm plaq}
\\
&\Downarrow\quad \text{finite sums}
\\
&S_{\rm bulk}^{(b)},\ S_{\rm temporal}^{(b)}
  \in \mathcal A_{\rm plaq}
\\
&\Downarrow\quad
  \text{Mathlib polynomial approximation}
\\
&K(b,\cdot)
  \in
  \overline{\mathcal A_{\rm plaq}}^{\|\cdot\|_\infty}.
\end{aligned}
\]

No abstract density axiom is introduced anywhere in this chain.

## 6. Current #10420 failure is local Lean elaboration, not mathematics or infrastructure

Fast Check #10420 reached fallback `lake build` successfully and built the two predecessor packages:

- `PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeaturePolynomialClosure`
- `PeriodicHypercubicEvenBoundaryCompletedPositiveGramFeaturePlaquetteGeneratorClosure`

The only new required target that failed was

`PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure`.

The primary errors were:

```text
failed to synthesize instance of type class
  Decidable (periodicHypercubicEvenStrictPositivePlaquette p)
```

and

```text
failed to synthesize instance of type class
  Decidable (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
```

followed by unsolved goals in the proposition-selected `ContinuousMap` equalities and the zero branches of the corresponding subalgebra-membership proofs.

The expected repair is local:

- introduce `classical` in the definitions/theorems using proposition selection, or otherwise supply the required `Decidable` instances;
- then simplify the positive/negative branches directly against `propositionIndicator` / the selected-term definitions;
- use `A.zero_mem` explicitly in the negative branch if simplification does not close the membership goal automatically.

This is an elaboration/API-shape issue. It does not invalidate the common-algebra construction or the green polynomial/finite-sum layers below it.

## 7. Next C⁰ step after the common plaquette algebra is green

After obtaining, for every boundary configuration `b`,

\[
 K(b,\cdot)
 \in
 \overline{\mathcal A_{\rm plaq}},
\]

the raw function should be treated as a Banach-space-valued integral rather than only as a pointwise scalar integral.

Define conceptually

\[
 \Phi(b)
 =
 p(b)\,\psi_{\partial}(b)\,K(b,\cdot)
 \in C(X,\mathbb R).
\]

Then

\[
 g_{\rm raw}
 =
 \int_{\partial}\Phi(b)\,d\mu(b)
\]

as a Bochner integral in the Banach space `C(X, ℝ)`.

The desired route is:

1. prove joint continuity of

   \[
   (b,x)\mapsto
   \operatorname{boundaryFiberedAssemble}(b,x,1),
   \]

2. propagate joint continuity through plaquette holonomy, Wilson energy, finite actions, exponentials and the completed-positive feature;
3. use the compact-domain `ContinuousMap` exponential-law interface (e.g. `ContinuousMap.continuous_of_continuous_uncurry`) to obtain continuity of

   \[
   b\mapsto K(b,\cdot)
   \]

   in the sup norm;
4. combine this with the already-proved integrability of the boundary vacuum wavefunction and boundedness of the probe/kernel to obtain Bochner integrability of `Phi`;
5. use closedness/linearity of `\overline{\mathcal A_{\rm plaq}}` to show the Bochner integral remains in that closed subspace;
6. identify the Bochner integral pointwise with the already-existing raw `ContinuousMap`.

The existing theorem

```lean
FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_continuous_positive
```

already proves continuity in `x` for fixed `b`. Its proof is coordinatewise, so the joint `(b,x)` version should be an additive strengthening rather than a new analytic construction.

## 8. Final finite-to-physical lift still required

Even after proving

\[
 g_{\rm raw}
 \in
 \overline{\mathcal A_{\rm plaq}},
\]

one must still relate the actual finite plaquette algebra to the theorem-generated finite positive-half OS observables.

The target inclusion is

\[
 \mathcal A_{\rm plaq}
 \subseteq
 \operatorname{range}(\mathrm{finitePositiveHalfObservable}),
\]

or an equivalent carrier-level statement strong enough to imply

\[
 \overline{\mathcal A_{\rm plaq}}
 \subseteq
 \overline{\operatorname{range}
   (\mathrm{finitePositiveHalfObservable})}.
\]

Using the already-green range equality then gives

\[
 g_{\rm raw}
 \in
 \overline{\operatorname{range}
   (Q.\mathrm{positiveHalfPullback}\,n)}.
\]

From there the existing pipeline is:

\[
\text{C⁰ range closure}
\to
\text{open-half Haar L² range closure}
\to
\text{reconstructed nonzero excitation}
\to
\text{Rayleigh/mass route}.
\]

The key point is that the remaining lift must be an **actual Wilson/cylinder/plaquette realization theorem**, not a generic `Dense` hypothesis.

## 9. Current proof frontier in one diagram

\[
\boxed{
\begin{array}{c}
\text{actual plaquette energies}\\
\downarrow\\
\text{finite positive bulk / temporal actions}\\
\downarrow\\
\text{Mathlib compact-range polynomial approximation}\\
\downarrow\\
K(b,\cdot)\in\overline{\mathcal A_{\rm plaq}}\\
\downarrow\quad\text{Bochner boundary integration}\\
g_{\rm raw}\in\overline{\mathcal A_{\rm plaq}}\\
\downarrow\quad\text{actual finite observable lift}\\
 g_{\rm raw}\in
 \overline{\operatorname{range}(Q.\mathrm{positiveHalfPullback}\,n)}\\
\downarrow\\
\text{C⁰→L²}\\
\downarrow\\
\text{nonzero reconstructed physical excitation}\\
\downarrow\\
\text{existing Rayleigh / physical Yang–Mills mass machinery}
\end{array}}
\]

At the time of this note, the first three arrows are green through the plaquette-generator reduction. The explicit common `Algebra.adjoin` realization is implemented but needs the local `Decidable` / indicator-branch elaboration repair identified by Fast Check #10420. The Bochner-integration and finite-observable-lift arrows are the subsequent mathematical frontier.

## 10. Safety / claim discipline

This note must not be read as claiming that the full Clay Yang–Mills mass-gap theorem is already discharged by the current PR.

In particular:

- no global surjectivity of the positive-half pullback is asserted;
- no abstract density assumption substitutes for actual finite Wilson observables;
- no duplicate Hilbert space is introduced;
- the static finite Wilson Gram operator is not identified with Euclidean time evolution;
- the exact mass `33/20` route and all existing physical/continuum assumptions remain unchanged;
- #10420 is not green and therefore `c45d7c071f6168ea867e079e2da1adde6df8e7c1` is not a green fixed point.

The safe green fixed point for the proof content recorded here is `20a0c88b41388f6f5c8bcbb9b72afc594654e4b7` / Fast Check #10419, with the common actual plaquette algebra as the immediate repair target.
