# MGAP4D Roadmap

This roadmap records the current proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-02 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

and the canonical exact checkpoint represented by this document is

```text
9bdd8906d9af8241a79a565d29cff8021681f817
```

which is the normal merge of PR #3151,

```text
Reduce SU2 exact-gap seam to selected-mode matrix coefficients.
```

The public `main` branch is a landing surface. Only theorem results merged into the authoritative theorem carrier count as current proof status.

> **Current frontier**
>
> The proof-development frontier has moved well beyond the August 2026 shared-boundary Poincaré checkpoint. The canonical branch now contains completed finite-transfer spectral/logarithmic-generator machinery, transfer/Wightman common-core machinery, and an SU(2) exact-gap mode pipeline extending to a graph-closed vacuum-orthogonal Hamiltonian mode.
>
> The immediate model-facing seam is now much smaller: prove, from the literal finite Wilson one-slab model, the **selected-mode scalar pair-Haar matrix-coefficient identity** required by `CompletedBoundaryTransferOneSlabPairWeakAtFor`, while keeping the finite/common-time normalization coherent and explicit.
>
> This does **not** mean that the Clay Millennium problem is solved. The raw one-slab bridge is still open, the exact-mode statement is not automatically a global spectral lower bound, and the selected scalar continuum process is not yet the complete four-dimensional Yang--Mills field.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated implication machinery** — the theorem chain is formalized, but a model-facing input remains.
- **Conditional model theorem** — mathematically proved under an explicit model-facing hypothesis not yet derived from the raw Wilson root.
- **Open now** — immediate constructive frontier.
- **Open downstream** — required after the current frontier.
- **Diagnostic only** — correct theorem or obstruction that is not the active mass-gap mechanism.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model                        [Integrated]
  -> reflection positivity / OS boundary geometry                    [Integrated]
  -> spatial-slice and boundary Haar-L² carriers                     [Integrated]
  -> normalized physical one-slab transfer                           [Integrated]
  -> completed excitation-pair transfer                              [Integrated]
  -> positivity / compact spectral support                           [Integrated]

B. SAME-ROOT SCALAR CONTINUUM OS

finite Wilson scalar readout                                         [Integrated]
  -> rational path law / Prokhorov continuum law                     [Integrated]
  -> continuum OS positivity                                         [Integrated]
  -> direct-limit Hilbert carrier                                    [Integrated]
  -> real C₀ contraction semigroup                                   [Integrated]
  -> graph-closed self-adjoint OS Hamiltonian                        [Integrated]
  -> normalized vacuum Ω / complete Ω⊥                              [Integrated]

C. TRANSFER SPECTRAL / LOG-GENERATOR LANE

positive compact one-step transfer                                   [Integrated]
  -> strictly-positive spectral support                              [Integrated]
  -> partially-defined logarithmic generator                         [Integrated]
  -> resolvent / moment / effective-energy hierarchy                 [Integrated]
  -> intrinsic logarithmic spectral floor                           [Integrated]
  -> actual point-energy-set identification                          [Integrated]

D. TRANSFER / WIGHTMAN COMMON-CORE LANE

spectral modes                                                       [Integrated]
  -> algebraic spectral span dense in support                        [Integrated]
  -> Mathlib LinearPMap.HasCore                                      [Integrated]
  -> common-core Hilbert equivalence / self-adjoint closure          [Integrated]
  -> mode-wise target action -> full intertwining                    [Integrated implication machinery]
  -> transfer point energies <-> Wightman H|Ω⊥ energies             [Integrated implication machinery]
  -> attained Wightman mass-gap certificate                          [Integrated implication machinery]

E. SU(2) EXACT-GAP COMMON-CARRIER LANE

cutoff physical transfer mode                                        [Integrated model object]
  -> boundary realization                                            [reduced to closure / graph theorems]
  -> completed boundary transfer                                     [Integrated]
  -> finite OS time-one eigenmode                                    [Integrated implication machinery]
  -> common-carrier continuum mode                                   [Integrated implication machinery]
  -> exactGapClusterContractionRatio                                 [Integrated implication machinery]
  -> graph-closed Ω⊥ Hamiltonian mode at exactGapValueReal           [Integrated implication machinery]

F. CURRENT ONE-SLAB SEAM

selected SU(2) mode f_n + normalized top mode ω_n
  -> literal one-slab Wilson kernel coefficient                      [existing finite kernel machinery]
  -> translated/synthesized OS coefficient                           [needs explicit connection]
  -> scalar equality for every pair-Haar test z                      [OPEN NOW]
  -> CompletedBoundaryTransferOneSlabPairWeakAtFor                    [OPEN NOW]
  -> exact completed-boundary mode equation                          [already generated]
  -> downstream exact-gap chain                                      [already generated]

G. FULL PHYSICAL MASS GAP / CLAY COMPLETION

exact selected mode != global spectral gap                           [must bridge]
selected scalar continuum != full 4D gauge field                     [must enlarge]
full same-root OS/Wightman physical carrier                           [OPEN]
strictly positive spectrum above vacuum                              [OPEN]
Clay-level existence + mass gap                                      [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository-operation rules for theorem work:

```text
start from the exact authoritative canonical SHA
validate proof units on a Draft PR
accept CI only when workflow / job / exact Lean step are terminal success
never treat queued or in_progress as a validation receipt
repair a failed head only after the failure is terminal and inspected
keep proof changes additive / tighten-only unless correcting an error
forbid sorry / admit / axiom / placeholder-constant escapes
close the validation Draft unmerged after exact-head success
create a same-base / same-head non-Draft replacement
require independent exact-head CI on the replacement
fresh-check head/base/mergeability/reviews/threads before merge
normal merge with expected head SHA pinned
record GitHub's returned merge SHA as authoritative
verify merge parent 1 = old canonical and parent 2 = proof head
verify the canonical branch points exactly at the merge SHA
```

Claim discipline:

```text
finite theorem != continuum theorem
selected scalar process != full 4D Yang--Mills field
one positive eigenmode != global spectral gap
conditional transfer/Wightman bridge != constructed physical bridge
symbolic exactGapValueReal != a numerical literal without an explicit theorem
static Dobrushin clustering != physical continuum mass gap
```

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The finite root is the actual periodic-even compact special-unitary Wilson Gibbs model.

Integrated components include

```text
oriented lattice / edge / plaquette geometry
normalized Haar probability structure
Wilson action / Gibbs density / probability measure
reflection-fixed geometry and positive-time decomposition
finite Wilson reflection positivity
boundary and spatial-slice coordinate systems
gauge-covariant holonomy
gauge-invariant normalized trace observables
integer temporal translation / reflection covariance
finite support geometry
```

Permanent rule: keep the interacting Wilson marginal and actual finite source visible through every bridge. Do not replace the model by an abstract probability space at the decisive step.

---

# Phase 2 — Same-root primary scalar continuum law

**Status: Integrated.**

The constructive continuum lane uses a primary gauge-invariant scalar Wilson readout.

Integrated route:

```text
finite primary positive-half readout
  -> reflection-completed rational-time path
  -> scalar path carrier ℚ -> ℝ
  -> tight finite pushforward laws
  -> Prokhorov subsequential continuum probability law
```

This is a genuine same-root continuum observable process. It is not yet the complete gauge field on `ℝ⁴`.

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

This phase is no longer the immediate blocker.

---

# Phase 4 — Completed finite physical transfer

**Status: Integrated.**

The finite physical transfer program has been pushed from lattice kernels into completed Hilbert-space operators.

Key achievements include

```text
physical spatial-slice gauge-invariant L² submodules
one-slab physical transfer
excitation-pair external tensors
algebraic tensor-square transfer
completed pair-Hilbert transfer
self-adjoint contraction structure
positivity via Schur/Hadamard-product arguments
compact positive spectral decomposition
```

Boundary and ordered spatial-slice pair coordinates are linked by exact inverse linear isometries. These are now used directly in the current one-slab seam.

---

# Phase 5 — Generator, resolvent, and intrinsic spectral floor

**Status: Integrated.**

The finite completed transfer lane now contains a substantial spectral calculus rather than only a coarse norm estimate.

Canonical milestones include

```text
transfer/generator affine spectral relations
positive resolvent branches
below-gap coercive resolvents
above-one resolvent calculus
all-order scalar derivative recurrences
strictly-positive transfer spectral support
-log transfer spectral energy
partially-defined self-adjoint logarithmic generator
actual generator eigenmodes from transfer spectral modes
converse recovery of spectral coordinates from generator eigenmodes
point-energy set = logarithmic transfer spectrum
intrinsic spectral floor = point-energy infimum
resolvent-moment / effective-energy variational identifications
```

Representative later milestone: PR #2947 identifies the variational floor with the actual log-generator point spectrum while keeping the finite-volume coercive scale only as a lower bound.

---

# Phase 6 — Transfer / Wightman operator bridge

**Status: Integrated implication machinery; model realization remains relevant.**

The transfer/Wightman bridge has been systematically tightened.

Historical reduction:

```text
global Hilbert equivalence + global domain transport
  -> common dense-core realization
  -> closed-subspace corestriction
  -> one source HasCore + self-adjoint maximality
  -> canonical positive-transfer spectral span
  -> theorem-generated source HasCore
  -> mode-wise Wightman domain/action equations
```

Important integrated milestones include

```text
PR #2955  operator-level transfer/Wightman point-energy transport
PR #2959  terminal mass-gap certificate implications
PR #2965  generated Hilbert equivalence from one common dense core
PR #3008  generated intertwining from one self-adjoint common core
PR #3020  canonical transfer spectral core
PR #3028  mode-wise transfer/Wightman core identities
PR #3030  exponential OS semigroup orbit -> graph-closed Hamiltonian mode
```

The conceptual gain is important: the bridge no longer asks for an arbitrary global spectral equality. It is generated from local/core model equations plus self-adjoint closure.

---

# Phase 7 — SU(2) physical transfer modes and the common carrier

**Status: Integrated implication machinery; raw model realization progressively reduced.**

The SU(2) lane connects normalized physical one-slice transfer modes to the common finite/continuum OS carrier.

The realization seam was tightened through the following sequence:

```text
exact boundary witness
  -> boundary moment closure
  -> positive-half synthesis closure
  -> positive-time-submodule closure
  -> direct synthesized boundary-pair closure
  -> completed transfer graph closure
  -> exact completed transfer criterion
```

Representative milestones:

```text
PR #3078  range of completed OS boundary embedding = closure of canonical Wilson moments
PR #3088  reduce physical transfer realization to actual positive-half synthesis
PR #3096  move the sequence directly into the positive-time submodule
PR #3108  package the condition as synthesized boundary-pair closure
PR #3123  identify positive-time boundary-pair graph closure
PR #3127  strengthen closure to exact completed transfer graph equality
PR #3133  reduce closure to the completed-boundary criterion
```

No ambient boundary-`L²` surjectivity is introduced.

---

# Phase 8 — Exact-gap common-carrier specialization

**Status: Integrated implication machinery.**

PR #3118 specializes the common-carrier mode theorem to

```text
exactGapClusterContractionRatio = exp (-exactGapValueReal)
```

and generates, once the finite realization hypotheses are met,

```text
continuum OS time-one eigenvalue
  = exactGapClusterContractionRatio
```

followed by a graph-closed vacuum-orthogonal Hamiltonian mode with energy

```text
exactGapValueReal.
```

Important claim boundary: this theorem deliberately does not manufacture a downstream numerical-literal equality for `exactGapValueReal`.

---

# Phase 9 — Collapse the post-boundary exact-gap seam

**Status: Integrated.**

The remaining post-synthesis seam was then reduced in several steps.

```text
PR #3138
  boundary membership is generated from the common-carrier boundary identity;
  the only post-boundary condition becomes
    K_(n,2) x_n = x_n^(1).

PR #3142
  replace the mode-specific boundary equation by structural one-slab pair intertwining
  after conjugating the completed boundary operator to ordered spatial-slice pair L².

PR #3146
  replace strong pair-vector equality by equality of all real pair-Haar matrix coefficients.

PR #3151
  remove quantification over all endpoint pairs;
  retain only one selected physical mode f_n and the normalized one-slab top mode ω_n.
```

This is the most important current roadmap update.

The exact-gap mode chain now consumes the pointwise property

```lean
CompletedBoundaryTransferOneSlabPairWeakAtFor
```

for the selected pair only.

---

# Phase 10 — Prove the selected-mode scalar one-slab identity from the Wilson kernel

**Status: OPEN NOW.**

This is the immediate mathematical target.

For each cutoff `n`, selected gauge-invariant mode `f_n`, normalized top mode `omega_n`, and arbitrary test vector `z` in the ordered pair-Haar `L²` carrier, prove equality between

```text
< conjugated completed OS boundary transfer of (f_n ⊠ omega_n), z >
```

and

```text
< (T_one-slab f_n) ⊠ (T_one-slab omega_n), z >.
```

The right-hand side is naturally compatible with the already-developed literal Wilson one-slab kernel / Hilbert-Schmidt matrix-coefficient machinery.

The proof should be model-derived. The intended ingredients are:

```text
finite integer temporal configuration translation
Wilson Gibbs translation invariance
positive-time observable pullback / synthesis
boundary <-> ordered spatial-slice pair isometries
literal one-slab normalized kernel
Fubini / product-Haar integration
Hilbert-Schmidt kernel pairing
one-slab normalization / top-mode normalization
```

Forbidden shortcut:

```text
do not assume the finite OS eigen-equation or the downstream exact-gap Hamiltonian equation
in order to prove the one-slab bridge that is supposed to generate them.
```

Completion criterion:

```text
for the exact selected mode family f_n,
SU2CompletedBoundaryTransferPhysicalModeWeakAt n (f_n)
is proved from the finite Wilson model rather than supplied as a hypothesis.
```

---

# Phase 11 — Make finite/common-time coherence explicit

**Status: OPEN NOW, coupled to Phase 10.**

The abstract approximating semigroup family carries a translation

```text
C.translate : NNReal -> ...
```

and the exact-gap common-carrier lane currently uses time `1`.

The finite discrete physical action separately carries integer lattice translation together with the physical time map

```text
k |-> k * latticeSpacing n.
```

These are not definitionally the same object in the current structures.

Required work:

```text
identify the intended dimensionless OS one-step convention;
state the finite/common time map explicitly;
prove that the translated finite observable used by the OS construction matches the
concrete one-slab Wilson translation at the time required by the transfer theorem;
do not hide a cutoff-dependent rescaling in simp or definitional equality.
```

Completion criterion: the theorem feeding Phase 10 makes the time normalization explicit and typechecks without an unproved identification between abstract `C.translate 1` and the concrete lattice action.

---

# Phase 12 — Close the exact-gap selected-mode chain from raw model data

**Status: Open downstream; implication machinery already integrated.**

Once Phases 10 and 11 are discharged, the existing canonical theorems are designed to produce

```text
raw Wilson selected-mode scalar identity
  -> exact completed-boundary one-slab equation
  -> genuine finite Wilson OS time-one eigenmode
  -> common-carrier continuum time-one eigenmode
  -> exactGapClusterContractionRatio
  -> graph-closed Ω⊥ Hamiltonian mode at exactGapValueReal.
```

At that point the mode existence statement would be model-derived rather than conditional on a selected-mode matrix-coefficient hypothesis.

This still must not be advertised automatically as the full Yang--Mills mass-gap theorem.

---

# Phase 13 — Global spectral lower bound above the vacuum

**Status: Open / partially integrated through several routes.**

A single attained positive mode and a global spectral gap are different statements.

The repository has two relevant mechanisms:

### Route A — spectral-floor identification

Use the completed positive-transfer logarithmic spectral floor, the transfer/Wightman common-core bridge, and the same-root physical realization to show that the positive attained value is the bottom of the full non-vacuum spectrum on the intended physical Hamiltonian carrier.

### Route B — uniform coercive/Poincaré estimate

Prove a genuine scale-uniform finite Wilson estimate such as

```text
(1 - exp(-m t)) * ‖v‖²
  <= ‖v‖² - ‖K_(n,t) v‖²
```

for all relevant vacuum-orthogonal boundary vectors and propagate it through the existing finite-to-continuum gap-transfer machinery.

The old README treated Route B as the single immediate frontier. The current roadmap instead treats it as a complementary **global lower-bound route**, while the exact selected-mode one-slab identity is the immediate constructive frontier.

Completion criterion for a mass-gap statement on a fixed Hamiltonian carrier:

```text
there exists m > 0 such that
spectrum(H) ∩ (0,m) = ∅
and m is attained or the positive spectral infimum is otherwise controlled,
with Ω the vacuum of the same carrier.
```

---

# Phase 14 — Dobrushin covariance route

**Status: Diagnostic only for the intended high-β continuum mechanism.**

The finite static covariance theorem remains correct.

For the active majorant

```text
q(beta) = (exp(4 beta)-1)/(exp(4 beta)+1)
```

the canonical theorem proves

```text
q(beta) -> 1
18 q(beta) -> 18
```

as `beta -> +∞`.

Therefore a scale-independent Dobrushin ratio `< 1` cannot survive such a high-β scaling. Do not redirect the immediate proof sequence back to this mechanism unless a genuinely different model-derived estimate is introduced.

---

# Phase 15 — Full four-dimensional Yang--Mills construction

**Status: OPEN.**

The same-root scalar path construction is not yet a complete four-dimensional continuum gauge field.

A Clay-level existence theorem requires one coherent physical model carrying the necessary combination of

```text
nontrivial continuum local gauge-invariant observables / gauge structure
Euclidean covariance
reflection positivity
regularity / distributional control
OS reconstruction
Wightman reconstruction where required
vacuum structure
physical clustering / spectral structure
and a strictly positive mass gap
```

with every essential bridge traced back to the finite Wilson root or a proved continuum limit.

The repository should not claim completion until this carrier exists and the mass-gap theorem is stated on it without residual certificate-style assumptions.

---

# Phase 16 — Exact numerical value and public theorem surface

**Status: Separate claim layer.**

The public formal chain currently uses the symbolic

```text
exactGapValueReal.
```

Any theorem identifying that value with a numerical literal belongs in a separate, explicit bridge. It must preserve the provenance from

```text
finite Wilson model
-> transfer spectral object
-> continuum / Wightman Hamiltonian
-> physical non-vacuum spectrum.
```

Do not add a presentation-only equality that bypasses this route.

---

# Phase 17 — External audit and release

**Status: Open downstream.**

Before any claim substantially stronger than the current repository description, require an external audit package containing at least

```text
exact canonical SHA
Lean / mathlib toolchain version
zero forbidden-proof-token receipt
full changed-Lean CI receipts
list of model-facing assumptions remaining in public terminal theorems
finite Wilson -> continuum dependency map
OS / Wightman carrier dependency map
spectral-floor / exact-mode dependency map
statement-by-statement claim-boundary review
```

The audit should distinguish Lean elaboration success from mathematical completeness of the physical construction.

---

# Immediate next mathematical unit

The next proof unit should be coherent and model-facing rather than another downstream wrapper:

```text
Goal:
  derive SU2CompletedBoundaryTransferPhysicalModeWeakAt
  for the selected exact-gap mode family directly from the finite one-slab Wilson model.

Preferred route:
  1. expose the OS-side selected pair matrix coefficient;
  2. rewrite the finite translated/synthesized expression as an explicit Wilson integral;
  3. rewrite the one-slab transfer side using the canonical normalized kernel pairing;
  4. use product-Haar Fubini and the boundary/pair isometries;
  5. prove the two scalar expressions equal;
  6. keep the finite/common-time rescaling visible;
  7. invoke the already-canonical weak-to-strong and exact-gap wrappers.

Do not:
  assume the finite OS eigen-equation;
  assume the continuum eigen-equation;
  assume the Hamiltonian eigen-equation;
  identify C.translate 1 with lattice one-step by fiat;
  replace the interacting Wilson measure by Haar measure.
```

After that unit, re-evaluate whether the remaining global mass-gap obligation is best closed through the intrinsic spectral-floor/Wightman route, the uniform coercive route, or a theorem showing that the two canonical routes coincide on the final physical carrier.
