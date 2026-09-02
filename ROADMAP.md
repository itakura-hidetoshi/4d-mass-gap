# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-03 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

and the canonical exact checkpoint represented here is

```text
cfa8a7b31f1904699371882270fde21885a99079
```

which is the normal merge of PR #3197,

```text
Expose realizable one-step synthesis in raw Wilson path Gram form.
```

The public `main` branch is a landing surface. Only theorem results merged into the authoritative theorem carrier count as current proof status.

> **Current frontier**
>
> The previous public roadmap stopped at PR #3151, where the `SU(2)` exact-mode realization seam had been reduced to selected pair-Haar matrix coefficients. The canonical branch has since pushed that seam upstream through raw one-slab coefficients, dense actual synthesis, explicit finite/common one-step coherence, projected synthesis density, a realizable raw-kernel limit predicate, literal one-lattice-step open-half representatives, and finally the raw normalized unfixed `H+1`-slab Wilson path Gram representative.
>
> A crucial temporal-gauge ingredient is already canonical: for Gauss-law terminal states, normalized temporal-link product Haar integration of the unfixed positive-half endpoint amplitude equals the temporal-gauge spatial-path amplitude.
>
> The immediate task is therefore the remaining **finite Markov/Fubini decomposition** that extracts the adjacent temporal-gauge one-slab Wilson coefficient from the current raw positive-half path expression and thereby proves `RealizableOneStepPhysicalTopRawKernelLimitAtFor` for the selected mode family.
>
> This is not yet a Clay-level theorem. The common-semigroup/actual-lattice one-step equality remains an explicit model-facing coherence statement; one selected exact mode is not a global spectral lower bound; and the same-root scalar continuum process is not yet the full four-dimensional Yang--Mills field.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated implication machinery** — the theorem chain is formalized, but a model-facing input remains.
- **Explicit model seam** — the missing input is isolated as a named proposition with no hidden downstream conclusion.
- **Open now** — immediate constructive frontier.
- **Open downstream** — required after the current frontier.
- **Diagnostic only** — correct theorem or obstruction that is not the active mass-gap mechanism.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model                        [Integrated]
  -> reflection positivity / OS boundary geometry                    [Integrated]
  -> boundary and spatial-slice Haar-L² carriers                     [Integrated]
  -> normalized physical one-slab transfer                           [Integrated]
  -> completed pair transfer                                         [Integrated]
  -> positivity / compact spectral support                           [Integrated]

B. SAME-ROOT SCALAR CONTINUUM OS

finite Wilson scalar readout                                         [Integrated]
  -> rational path law / Prokhorov continuum law                     [Integrated]
  -> continuum OS positivity                                         [Integrated]
  -> direct-limit real Hilbert carrier                               [Integrated]
  -> real C₀ contraction semigroup                                   [Integrated]
  -> graph-closed self-adjoint OS Hamiltonian                        [Integrated]
  -> normalized vacuum Ω / complete Ω⊥                              [Integrated]

C. TRANSFER SPECTRAL / LOG-GENERATOR LANE

positive compact transfer                                            [Integrated]
  -> strictly-positive spectral support                              [Integrated]
  -> partial logarithmic generator                                   [Integrated]
  -> resolvent / moment / effective-energy hierarchy                 [Integrated]
  -> intrinsic logarithmic spectral floor                            [Integrated]
  -> actual point-energy-set identification                          [Integrated]

D. TRANSFER / WIGHTMAN COMMON-CORE LANE

transfer spectral modes                                              [Integrated]
  -> canonical source operator core                                  [Integrated]
  -> common-core Hilbert equivalence / closure machinery             [Integrated]
  -> mode-wise target action -> full intertwining                    [Integrated implication machinery]
  -> transfer energies <-> Wightman H|Ω⊥ energies                   [Integrated implication machinery]
  -> attained-gap certificate implications                           [Integrated implication machinery]

E. SU(2) EXACT-MODE LANE

selected physical mode f_n + normalized top mode ω_n
  -> completed boundary / pair realization                           [Integrated implication machinery]
  -> selected weak coefficient seam                                  [reduced further]
  -> raw one-slab Wilson coefficient                                 [Integrated]
  -> actual realizable synthesis density                             [Integrated]
  -> literal one-lattice-step open-half representative               [Integrated]
  -> raw normalized unfixed H+1-slab Gram representative             [Integrated]

F. CURRENT FINITE PATH-INTEGRAL SEAM

raw H+1-slab boundary/open-half Gram coefficient
  -> endpoint-amplitude/product-Haar formulation                     [OPEN NOW]
  -> Gauss endpoint temporal-link Haar reduction                     [Integrated]
  -> temporal-gauge path Markov/Fubini decomposition                 [OPEN NOW]
  -> adjacent temporal-gauge one-slab coefficient                    [OPEN NOW]
  -> RealizableOneStepPhysicalTopRawKernelLimitAtFor                 [OPEN NOW]
  -> selected completed-boundary weak identity                       [already generated]
  -> continuum exact mode / graph-closed Hamiltonian mode            [already generated]

G. SEPARATE COHERENCE SEAM

C.translate 1 = R.positiveTranslation n 1                            [Explicit model seam]

H. GLOBAL MASS GAP / FULL 4D YM

selected exact mode -> global spectral lower bound                   [OPEN]
scalar continuum -> sufficiently rich 4D YM field/state              [OPEN]
full same-root OS/Wightman physical carrier                          [OPEN]
strictly positive spectrum above vacuum                              [OPEN]
Clay-level existence + mass gap                                      [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

The theorem workflow is intentionally conservative:

```text
start from the exact authoritative canonical SHA
validate theorem units on Draft PRs
accept CI only after workflow / job / exact Lean step are terminal success
never count queued or in_progress as a validation receipt
inspect terminal failures before changing the proof head
keep proof changes additive / tighten-only unless correcting an error
forbid sorry / admit / axiom / placeholder-constant escapes
close successful validation Drafts unmerged
create independent non-Draft replacements from a fresh canonical base
require independent exact-head CI on the replacement
fresh-check base/head/mergeability/reviews/threads before merge
normal merge with expected proof-head SHA pinned
verify GitHub's merge SHA and both merge parents
verify the canonical branch points exactly at the merge SHA
```

Claim discipline:

```text
finite theorem != continuum theorem
selected scalar process != full 4D Yang--Mills field
one positive eigenmode != global spectral gap
conditional/common-core implication machinery != constructed full physical bridge
symbolic exactGapValueReal != a numerical literal without a Lean theorem
finite Dobrushin clustering != physical continuum mass gap
```

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The finite root is the actual periodic-even compact special-unitary Wilson Gibbs model.

Integrated components include

```text
oriented lattice / edge / plaquette geometry
normalized compact Haar probability structure
Wilson action / Gibbs density / probability measure
reflection-fixed geometry and positive-time decomposition
finite Wilson reflection positivity
boundary and spatial-slice coordinate systems
gauge-covariant holonomy
gauge-invariant normalized trace observables
integer temporal translation / reflection covariance
finite support geometry
```

Permanent rule: keep the interacting Wilson source visible through decisive bridges. Do not replace the model by an unrelated abstract probability space at the point where the finite Wilson identity must be proved.

---

# Phase 2 — Same-root primary scalar continuum law

**Status: Integrated.**

The constructive continuum lane uses a primary gauge-invariant scalar Wilson readout.

```text
finite primary positive-half readout
  -> reflection-completed rational-time path
  -> scalar path carrier ℚ -> ℝ
  -> tight finite pushforward laws
  -> Prokhorov subsequential continuum probability law
```

This is a genuine same-root continuum observable process. It is not yet the full gauge field or complete local observable theory on `ℝ⁴`.

---

# Phase 3 — Continuum OS Hilbert reconstruction and real Hamiltonian

**Status: Integrated.**

Integrated chain:

```text
continuum rational-cylinder OS positivity
continuum reflection invariance
OS null quotient
fixed-slot real Hilbert completions
isometric directed system
completed direct-limit carrier
rational contraction semigroup
NNReal strongly continuous contraction semigroup
right generator / right Hamiltonian
graph closure as Mathlib LinearPMap
self-adjoint closed Hamiltonian
resolvent / Yosida recovery
normalized vacuum Ω
complete vacuum-orthogonal sector Ω⊥
```

This phase is not the immediate blocker.

---

# Phase 4 — Completed finite physical transfer

**Status: Integrated.**

The finite transfer program has been lifted from explicit kernels to completed Hilbert-space operators.

```text
physical spatial-slice gauge-invariant L² submodules
one-slab physical transfer
excitation-pair external tensors
completed pair-Hilbert transfer
boundary <-> ordered endpoint-pair isometries
self-adjoint contraction structure
positivity via finite tensor / Schur-product arguments
compact positive spectral decomposition
```

The current raw-model seam uses these exact boundary/pair coordinate maps rather than assuming a new ambient isomorphism.

---

# Phase 5 — Logarithmic generator, resolvent, and intrinsic spectral floor

**Status: Integrated.**

Canonical milestones include

```text
transfer/generator affine spectral relations
positive resolvent branches
below-gap coercive resolvents
above-one resolvent calculus
all-order scalar derivative recurrences
strictly-positive transfer spectral support
-log transfer spectral energy
partial self-adjoint logarithmic generator
transfer spectral modes -> generator eigenmodes
converse recovery of spectral coordinates
point-energy set = logarithmic transfer spectrum
intrinsic spectral floor = point-energy infimum
resolvent-moment / effective-energy variational identifications
```

This machinery remains available both to the exact-mode lane and to future global lower-bound work.

---

# Phase 6 — Transfer / Wightman common-core bridge

**Status: Integrated implication machinery.**

The bridge has been systematically tightened:

```text
global Hilbert equivalence + global operator intertwining
  -> common dense-core realization
  -> closed-subspace corestriction
  -> one source HasCore + self-adjoint maximality
  -> canonical positive-transfer spectral span
  -> theorem-generated source core
  -> mode-wise Wightman domain/action equations
```

The logical gain is that full operator statements can be generated from local/core model equations. The remaining physical task is to derive the required target realization identities from the same Wilson/continuum construction, not to assume a global spectral equality.

---

# Phase 7 — `SU(2)` selected exact-mode reduction through PR #3151

**Status: Integrated implication machinery.**

The post-boundary exact-mode seam was reduced through

```text
completed-boundary transfer equation
  -> pair-coordinate one-slab intertwining
  -> equality of all pair-Haar matrix coefficients
  -> one selected physical mode f_n paired with normalized top mode ω_n
```

At PR #3151 the downstream finite/continuum/Hamiltonian wrappers needed only the selected weak scalar coefficient statement, not an all-input operator identity.

This is now historical context: the current canonical branch has reduced that weak statement further upstream.

---

# Phase 8 — Rewrite the selected one-step side in literal Wilson language

**Status: Integrated.**

## PR #3157 — raw one-slab kernel coefficient

The selected one-step endpoint tensor coefficient is exactly a normalized Hilbert-Schmidt pairing built from the literal temporal-gauge one-slab Wilson transfer. Arbitrary ambient pair-Haar test vectors remain allowed.

## PR #3162 — dense actual synthesis approximation

Every completed finite OS state can be approximated by actual raw OS carriers whose Wilson adjoint-synthesis coefficients converge to the completed boundary-transfer coefficient.

File:

```text
PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransferSynthesisDensity.lean
```

## PR #3166 — finite/common one-step coherence predicate

The exact scale-local compatibility

```lean
R.CommonSemigroupOneStepCoherentAt hInvariant C n
```

was isolated as

```text
C.translate 1 = R.positiveTranslation n 1.
```

From this equality the code generates the corresponding carrier and synthesis identities. It does not claim the equality automatically for arbitrary `C`.

## PR #3171 — projected synthesis density

The synthesis-density theorem was extended to arbitrary ambient boundary inputs through the canonical projected inverse/compression, without assuming surjectivity of the boundary embedding.

## PR #3177 — raw-kernel limit seam

The old selected completed weak hypothesis is theorem-generated from the finite proposition

```lean
RealizableOneStepPhysicalTopRawKernelLimitAtFor
```

plus `CommonSemigroupOneStepCoherentAt`.

This proposition asks for convergence of actual one-lattice-step Wilson synthesis coefficients to the literal normalized one-slab coefficient for every pair-Haar test vector and every approximating raw-carrier sequence with the required projected physical-state limit.

It contains no continuum eigen-equation or Hamiltonian assumption.

---

# Phase 9 — Compute the actual realizable lattice step

**Status: Integrated.**

## PR #3181 — pointwise temporal-step formula

The canonical positive-half pullback after realizable integer lattice translation is identified pointwise with the original pullback evaluated on the literal finite temporal-section map.

File:

```text
PhysicalYangMillsGaugeInvariantOSCanonicalRealizablePositiveHalfTemporalStep.lean
```

## PR #3185 — open-half Haar-`L²` representative

The same formula is lifted to the actual open-half Haar-`L²` feature representative, including the one-step specialization.

File:

```text
PhysicalYangMillsGaugeInvariantOSCanonicalRealizablePositiveHalfL2TemporalStep.lean
```

This removes the need to reason about the one-step finite input through an opaque abstract semigroup action.

---

# Phase 10 — Rewrite actual synthesis as a raw positive-half Wilson Gram expression

**Status: Integrated.**

## PR #3191 — actual synthesis pair coefficient

For every actual OS carrier and arbitrary pair-Haar test `z`, the one-step adjoint-synthesis coefficient is exactly the canonical rectangular Hilbert-Schmidt Wilson Gram-kernel pairing.

File:

```text
PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisPairKernel.lean
```

## PR #3197 — raw `H+1`-slab path Gram representative

The rectangular completed positive-boundary Gram `L²` kernel is shown almost everywhere equal to the literal partition-normalized unfixed positive-half Wilson path kernel in canonical closure-transfer coordinates.

The same unit also exposes the pair-coordinate diagonal Gram identity

```text
<A† A z, z> = ‖A z‖².
```

File:

```text
PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisRawPathGram.lean
```

Important non-claim: the complete `H+1`-slab boundary Gram kernel is **not** identified with a single adjacent slab. The next step must derive the adjacent slab through finite path composition / Markov structure.

---

# Phase 11 — Temporal-link Haar gauge reduction

**Status: Integrated; no longer an open milestone.**

The canonical file

```text
PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction.lean
```

contains the exact theorem

```lean
periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_iteratedHaar_integral_eq_temporalGauge
```

For endpoint states `f,g` with gauge-invariant terminal state `g`, it proves

```text
integral over temporal-link product Haar
  of the unfixed positive-half endpoint amplitude
=
temporal-gauge spatial-path endpoint amplitude.
```

The proof uses a measure-preserving cumulative gauge transformation and Gauss-law a.e. invariance of the terminal endpoint. No terminal residual is canceled pointwise without that gauge-invariance input.

This theorem should be reused directly in the current proof; it should not be reproved under another name.

---

# Phase 12 — Extract the adjacent one-slab coefficient by finite Markov/Fubini decomposition

**Status: OPEN NOW.**

This is the immediate mathematical target after PR #3197.

Starting from the actual synthesis receipt, convert the raw rectangular Gram coefficient into a form compatible with the existing endpoint-amplitude temporal-gauge theorem and then prove the remaining finite path-composition identity.

Target schematic chain:

```text
actual one-step synthesis pair coefficient
  = rectangular Gram Hilbert-Schmidt pairing                  [Integrated]
  = normalized unfixed H+1-slab path expression               [Integrated a.e. kernel rep]
  -> endpoint-amplitude / explicit nested Haar integral        [OPEN]
  = temporal-gauge endpoint path amplitude                     [Integrated theorem]
  -> successive finite spatial-slice Haar integration          [OPEN]
  -> Markov / transfer composition                             [OPEN]
  -> adjacent temporal-gauge one-slab coefficient              [OPEN]
```

The right endpoint used in the exact-mode lane is the normalized top mode and is gauge invariant, so the existing Gauss endpoint theorem is designed for the relevant physical sector.

Expected ingredients:

```text
closure-transfer measure-preserving equivalence
boundary/open-half product Haar <-> explicit nested Haar
Fubini / product-measure integral identities
endpoint evaluation maps
existing temporal-gauge path kernel
adjacent one-slab temporal-gauge transfer kernel
one-slab top-mode equation / normalization
Hilbert-Schmidt pairing identities
```

Forbidden shortcuts:

```text
do not identify the entire H+1-slab kernel with one slab
do not assume the downstream finite OS eigen-equation
do not assume the continuum time-one eigen-equation
do not assume the Hamiltonian eigen-equation
do not replace arbitrary pair-Haar tests by pure tensors unless density is actually proved and used correctly
```

Completion criterion for this phase: prove the finite identity needed to discharge

```lean
R.RealizableOneStepPhysicalTopRawKernelLimitAtFor hInvariant n (f n)
```

for the selected `SU(2)` physical mode family.

---

# Phase 13 — Close the selected exact-mode chain from the finite seam

**Status: Open input; implication machinery already integrated.**

The file

```text
PhysicalYangMillsWilsonSU2CompletedBoundaryTransferRealizableOneStepRawKernelLimit.lean
```

already proves

```text
RealizableOneStepPhysicalTopRawKernelLimitAtFor
  + CommonSemigroupOneStepCoherentAt
    -> selected completed-boundary raw-kernel weak identity
    -> selected pair weak identity
    -> SU2CompletedBoundaryTransferPhysicalModeWeakAt
```

and re-exposes downstream continuum / exact-mode / graph-closed Hamiltonian theorems with the old opaque completed weak hypothesis removed.

Therefore once Phase 12 is complete, no new Hilbert-space separation theorem should be needed at this seam.

---

# Phase 14 — Prove finite/common-time coherence from the intended approximation model

**Status: Explicit model seam.**

The common family carries

```text
C.translate : NNReal -> ...
```

while the realizable finite model carries actual integer lattice translation

```text
R.positiveTranslation n k.
```

The code currently isolates the required one-step statement

```text
C.translate 1 = R.positiveTranslation n 1
```

as `CommonSemigroupOneStepCoherentAt`.

The realizable lattice action itself is now computed explicitly by PRs #3181/#3185. What remains is to derive the common-family equality from the intended scale/time construction rather than leave it as external data.

Required care:

```text
state the dimensionless / physical-time convention explicitly
make any lattice-spacing rescaling visible
do not hide cutoff-dependent time conversion in simp or definitional equality
prove only the coherence actually used by the downstream theorem
```

This phase is logically separate from the finite path-integral calculation in Phase 12, even though both are needed by the current exact-mode wrapper.

---

# Phase 15 — Global vacuum-orthogonal lower bound

**Status: Open downstream.**

One selected positive-energy Hamiltonian mode does not imply that no lower positive spectrum exists.

The repository's scale-uniform Poincaré/coercive machinery remains the natural complementary route toward a global lower bound, schematically

```text
(1 - exp(-m t)) * ‖v‖²
  <= ‖v‖² - ‖K_(n,t) v‖²
```

uniformly in the approximating scale.

Needed completion:

```text
model-derived uniform vacuum-orthogonal transfer estimate
  -> continuum semigroup decay / spectral lower bound
  -> exclusion of spectrum in (0,m)
```

If an exact mode at energy `m` is also available, the combination can potentially identify an attained spectral floor. The lower-bound theorem must be proved independently; it cannot be inferred from existence of the mode alone.

---

# Phase 16 — Full same-root four-dimensional Yang--Mills field/state

**Status: Open downstream; Clay-critical.**

The present same-root continuum construction is a selected scalar gauge-invariant process. A Clay-level existence theorem requires a sufficiently rich four-dimensional Yang--Mills continuum structure on one coherent physical model.

Required eventual package includes an appropriate formalization of

```text
Euclidean covariance
gauge structure / gauge-invariant local observables
reflection positivity
regularity / distributional control
physical nontriviality
vacuum and clustering
same-root OS/Wightman reconstruction
```

The exact mathematical formulation must be strong enough to represent the intended four-dimensional Yang--Mills theory, not merely one scalar projection of it.

---

# Phase 17 — Clay-level existence and mass gap

**Status: Open downstream.**

A final theorem would need the following on one coherent model-derived carrier:

```text
sufficiently rich 4D continuum Yang--Mills existence
+ model-derived OS/Wightman reconstruction
+ normalized vacuum
+ strictly positive spectral lower bound on Ω⊥
+ nontrivial physical excitations / attainment as required
=
Clay-level existence + mass gap
```

Until these bridges are proved, the repository must continue to describe itself as an advanced formalized constructive program rather than a completed Millennium-prize proof.

---

# Diagnostic lane — finite Dobrushin covariance

**Status: Integrated; diagnostic only for the scaling regime.**

The finite high-temperature theorem uses

```text
q(β) = (exp(4β)-1)/(exp(4β)+1)
```

with a geometric factor based on `18 q(β)`.

Since

```text
q(β) -> 1
18 q(β) -> 18
```

as `β -> +∞`, this mechanism cannot by itself yield a scale-independent `< 1` contraction in the large-`β` continuum scaling regime. It remains a valid finite theorem and an important obstruction diagnostic.

---

# Near-term proof order

The preferred order from the current canonical checkpoint is:

```text
1. keep canonical exact SHA fixed while investigating existing finite path lemmas;
2. express the #3197 raw rectangular pairing as an explicit endpoint nested-Haar integral;
3. reuse the existing Gauss endpoint iterated-Haar temporal-gauge theorem;
4. prove temporal-gauge finite path Markov/Fubini decomposition into adjacent one-slab transfer;
5. discharge RealizableOneStepPhysicalTopRawKernelLimitAtFor for the selected SU(2) mode family;
6. separately discharge CommonSemigroupOneStepCoherentAt from the actual approximation/time convention;
7. invoke the already-integrated selected exact-mode chain;
8. continue the independent global vacuum-orthogonal lower-bound program;
9. enlarge the same-root continuum theory from the selected scalar process to a sufficiently rich 4D Yang--Mills field/state;
10. close the full physical OS/Wightman and global spectral-gap theorem.
```

This ordering minimizes new abstract assumptions: each step should push the remaining hypotheses back toward the literal finite Wilson model or toward a clearly identified continuum-construction obligation.

---

# Key files for the immediate frontier

```text
MGAP4D/MathlibAnalytic/

PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisRawPathGram.lean
PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisPairKernel.lean
PhysicalYangMillsWilsonSU2CompletedBoundaryTransferRealizableOneStepRawKernelLimit.lean
PhysicalYangMillsGaugeInvariantOSCanonicalRealizablePositiveHalfTemporalStep.lean
PhysicalYangMillsGaugeInvariantOSCanonicalRealizablePositiveHalfL2TemporalStep.lean
PhysicalYangMillsGaugeInvariantOSCommonRealizableOneStepCoherence.lean
PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransferSynthesisDensity.lean
PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransferProjectedSynthesisDensity.lean
PeriodicHypercubicEvenBoundaryPositiveHalfClosureTransferKernelBridge.lean
PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction.lean
PeriodicHypercubicEvenSpecialUnitaryPositiveHalfClosureCylinderActionIdentification.lean
PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2TransferPositive.lean
PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2TransferFactorization.lean
```

The first question for any new proof unit should be: **does the required finite Haar/Fubini or transfer-composition theorem already exist under another name?** Reuse canonical mathlib-based identities before introducing parallel constructions.
