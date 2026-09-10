# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-10 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The current authoritative exact canonical SHA is

```text
2e294f5c9f95484c42809048cea4d08f284adba2
```

which is the normal merge commit of PR #3791,

```text
Build order-independent six-color spatial Wilson heat-bath block.
```

Its merge-push validation is

```text
PR Lean Fast Check #13491 = completed / success.
```

The public `main` branch is a landing/documentation surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status.

> **Current frontier**
>
> The former qualitative twelve-spatial obstruction is closed, and the next concrete locality layer is now substantially stronger than at the previous documentation checkpoint. Distinct same-six-color spatial links have exact Wilson plaquette separation, exact compact conditional-law locality, exact raw heat-bath commutation, and an order-independent bounded-continuous Feller color block.
>
> The immediate unresolved seam is **carrier compatibility**: transport the same-color structure to the genuine vacuum-weighted / ground-state Doob conditional-expectation carrier without adding an abstract independence assumption or silently identifying unrelated `L²` spaces.
>
> After that seam is closed, the central quantitative problem is to derive a positive **scale-independent** twelve-spatial Poincaré/coercivity coefficient on the genuine physical right-lifted top-orthogonal sector. The existing canonical routing then yields a physical transfer-gap lower bound `3κ/4`.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative theorem carrier.
- **Integrated implication machinery** — downstream implication is formalized, but a model-facing quantitative input remains.
- **Open now** — immediate constructive frontier.
- **Open next** — follows directly after the current carrier seam.
- **Open downstream** — required after the present quantitative frontier.
- **Parallel lane** — useful but not the current main obstruction.
- **Diagnostic only** — mathematically correct information that must not be mistaken for the missing theorem.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model                         [Integrated]
  -> reflection positivity / boundary geometry                       [Integrated]
  -> physical spatial-slice transfer                                 [Integrated]
  -> positive / strictly-positive ground-state transfer structure    [Integrated]

B. SAME-ROOT SCALAR CONTINUUM OS

finite Wilson scalar readout                                         [Integrated]
  -> rational/continuum scalar law                                   [Integrated]
  -> continuum OS positivity                                         [Integrated]
  -> direct-limit Hilbert carrier                                    [Integrated]
  -> real C₀ semigroup                                               [Integrated]
  -> graph-closed self-adjoint Hamiltonian                           [Integrated]
  -> vacuum Ω / complete Ω⊥                                          [Integrated]

C. FINITE PHYSICAL TRANSFER / PAIR THEORY

full top eigenspace F and K = Fᗮ                                     [Integrated]
  -> completed TT / NN decomposition inside PP                       [Integrated]
  -> finite-volume strict non-top contraction                        [Integrated]
  -> power decay / strong convergence                                [Integrated]
  -> fixed-space / coercivity / spectrum / resolvent / Green         [Integrated]
  -> exact reduced range / relative Poincaré                         [Integrated]

D. LOCAL WILSON / DOOB / HARNACK CONTROL

continuous positive physical vacuum                                 [Integrated]
  -> volume-independent one-link Harnack factor exp(8 beta)          [Integrated]
  -> Doob one-link conditional law                                   [Integrated]
  -> centered one-link resampling gap = 1                            [Integrated]
  -> exp(-16 beta) variance comparison                               [Integrated]
  -> native Wilson variance / L² projection-defect bridge            [Integrated]

E. GROUND-STATE TWELVE-SPATIAL GEOMETRY

one-slab ground-state joint probability law                          [Integrated]
  -> 6 right + 6 left genuine spatial condExp projections            [Integrated]
  -> common fixed by all 12 = a.e. constants                        [Integrated: #3746]
  -> kernel(E12) = intrinsic constant line                           [Integrated: #3773]
  -> E12(RUx)=0 <-> x=0 on physical K                               [Integrated: #3775]

F. SAME-COLOR WILSON LOCALITY AND HEAT-BATH COMMUTATION

same-color physical plaquette separation                             [Integrated: #3779]
  -> six-spatial-color plaquette separation                          [Integrated: #3781]
  -> compact Wilson neighbor/local-action separation                 [Integrated: #3783]
  -> exact normalized conditional-law locality                       [Integrated: #3787]
  -> exact six-color raw heat-bath commutation                       [Integrated: #3789]
  -> bounded-continuous Feller commutation                           [Integrated: #3791]
  -> RightCommutative fixed-color family                             [Integrated: #3791]
  -> permutation-independent six-color parallel Feller block         [Integrated: #3791]

G. PRESENT CARRIER SEAM

raw Wilson/Feller same-color block
  -> genuine vacuum-weighted / ground-state Doob conditional law     [OPEN NOW]
  -> same-color Doob commutation                                     [OPEN NOW]
  -> genuine order-independent six-color Doob block                  [OPEN NEXT]

H. PRESENT QUANTITATIVE FRONTIER

derive a model-facing block/variance estimate from the actual
Wilson/Doob/ground-state carrier                                     [OPEN NEXT]
  -> finite-volume coercive coefficient κ(H,N,beta) > 0              [OPEN NEXT]
  -> scale-independent lower bound κ > 0                             [OPEN NOW AFTER G]

  κ ||x||² <= E12,n(R U x)

for every scale n and x in physical K_n

  -> six-spatial frame coefficient 2κ                                [Integrated implication machinery]
  -> physical transfer gap >= 3κ/4                                  [Integrated implication machinery]
  -> scale-uniform positive physical transfer gap                    [OPEN DOWNSTREAM]

I. THERMODYNAMIC / CONTINUUM PHYSICAL PROPAGATION

uniform physical transfer gap                                       [OPEN DOWNSTREAM]
  -> stable Green / resolvent / decay bounds                         [OPEN DOWNSTREAM]
  -> controlled physical thermodynamic/scaling limit                 [OPEN DOWNSTREAM]
  -> physical OS/Wightman/Hamiltonian spectral lower bound           [OPEN DOWNSTREAM]

J. CLAY-LEVEL COMPLETION

full same-root 4D continuum gauge field/state                        [OPEN]
correct vacuum structure                                             [OPEN]
full physical OS/Wightman identification                             [OPEN]
strict positive continuum spectrum above vacuum                      [OPEN]
Clay-level existence + mass gap                                      [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository-operation rules for theorem work:

```text
start from the exact authoritative canonical SHA
use the theorem carrier, not public main, for theorem status
use GitHub-mediated repository operations
accept CI only at terminal success
never treat queued/in_progress as success
write-freeze while exact-head CI is running
inspect the first genuine Lean error before editing a failed head
keep theorem development additive/tighten-only
never weaken physical assumptions silently
never identify unrelated carriers silently
forbid sorry / admit / new axiom / placeholder theorem declarations
fresh-check exact head/base/mergeability/reviews/threads before merge
normal-merge with expected head SHA fixed
verify merge parents, branch pointer, and post-merge push CI
```

Current pinned environment:

```text
Lean    leanprover/lean4:v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

Permanent claim-discipline reminders:

```text
finite-volume theorem != continuum theorem
trivial kernel != quantitative coercivity
q_n < 1 for all n != inf_n(1-q_n)>0
mutual absolute continuity != uniform L² norm equivalence
raw Wilson locality != vacuum-weighted Doob locality without transport
pairwise commutation != Poincaré lower bound
local Harnack/TV comparison != global Poincaré without a theorem
selected vacuum vector != full top eigenspace
one exact mode != global spectral floor
same-root scalar continuum != full 4D Yang--Mills field
green open PR != merged canonical theorem
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
one-slab Wilson kernels and transfer operators
```

### Permanent rule

Keep the interacting Wilson model visible through every decisive physical bridge. Do not replace it by a product measure or abstract projection family unless an explicit theorem justifies that transport.

---

# Phase 2 — Same-root primary scalar continuum law

**Status: Integrated.**

Integrated route:

```text
finite primary gauge-invariant scalar readout
  -> reflection-completed rational-time path
  -> scalar path carrier ℚ -> ℝ
  -> tight finite pushforward laws
  -> Prokhorov subsequential continuum probability law
```

This is a same-root continuum observable process, not yet the complete gauge field on `ℝ⁴`.

---

# Phase 3 — Continuum OS Hilbert reconstruction and Hamiltonian

**Status: Integrated.**

Integrated chain:

```text
continuum rational-cylinder OS positivity
continuum reflection invariance
OS null quotient
fixed-slot real Hilbert completions
isometric directed system
completed direct-limit carrier
NNReal strongly continuous contraction semigroup
right generator / right Hamiltonian
graph closure as a mathlib linear partial operator
self-adjoint graph-closed Hamiltonian
resolvent / Yosida recovery
normalized vacuum Ω
complete vacuum-orthogonal sector Ω⊥
```

This phase is not the immediate blocker.

---

# Phase 4 — Transfer spectral / logarithmic-generator machinery

**Status: Integrated analytic machinery.**

Canonical infrastructure includes

```text
positive compact transfer spectral support
strictly-positive transfer support
partially-defined logarithmic generator
resolvent/effective-energy identities
intrinsic logarithmic spectral floor
spectral-mode eigenvector/domain theorems
canonical spectral span as an operator core
common-core Hilbert equivalence machinery
self-adjoint maximality / closure transfer
transfer point-energy <-> target Hamiltonian point-energy implications
mass-gap certificate implication machinery
```

This operator theory does not manufacture the missing model-derived scale-uniform coercivity.

---

# Phase 5 — Completed finite-volume physical transfer and pair geometry

**Status: Integrated.**

Let

```text
F  = full eigenvalue-one subspace of normalized one-slice physical transfer
K  = Fᗮ
PP = completed physical pair carrier
TT = completed top-top block
NN = completed non-top block inside PP
R  = one-slice orthogonal transfer restriction
q  = ||R||
S₂ = normalized physical pair transfer
```

The canonical chain includes

```text
TT ⟂ NN
PP = TT ⊕ NN
NN = PP ⊓ TTᗮ
q < 1 at fixed finite volume
non-top q^k-type power decay
strong convergence to the top-top projection
fixed-space characterization
coercivity / real spectral exclusion
resolvent estimates
non-top Green operator
exact reduced range
relative finite-volume Poincaré
```

### Current role

This is downstream infrastructure. The active proof program remains upstream: derive a scale-uniform quantitative constant from the actual ground-state Wilson dynamics.

---

# Phase 6 — Continuous-vacuum local Harnack and one-link Doob control

**Status: Integrated.**

The local model-facing route contains

```text
one-link Wilson action oscillation bound independent of volume
  -> one-slab kernel ratio <= exp(8 beta)
  -> pointwise continuous-vacuum Harnack control
  -> one-link Doob conditional probability law
  -> centered resampling residual = conditional variance
  -> centered one-link gap = 1
  -> raw Wilson variance * exp(-16 beta)
       <= continuous-vacuum Doob variance
  -> bounded-continuous Wilson observable bridge
  -> Gibbs-averaged conditional variance = global L² projection defect²
```

### Important boundary

These are one-link quantitative theorems. They do not by themselves say that two vacuum-weighted one-link laws at distinct same-color links are invariant under one another's resampling. That compatibility must be proved on the actual Doob carrier.

---

# Phase 7 — Genuine right six and left six spatial conditional expectations

**Status: Integrated.**

On the actual ground-state joint `L²` carrier:

```text
6 genuine right spatial conditional expectations
6 genuine left spatial conditional expectations
all are Hilbert orthogonal projections
one explicit 12-spatial family lives on the same joint carrier
all left six fix every right-boundary lift
```

The conventional residual satisfies

```text
E12(z) = 1/2 (E6,right(z) + E6,left(z))
```

and hence on right lifts

```text
E12(Ru) = 1/2 E6(u).
```

The implication

```text
12-spatial Poincaré κ
  -> six-spatial frame 2κ
  -> physical transfer gap >= 3κ/4
```

is integrated. Production of a uniform `κ` is not.

---

# Phase 8 — Six-color retained-coordinate elimination and common-fixed collapse

**Status: Integrated.**

Integrated milestones include

```text
#3711  ground-state joint and pair-Haar mutual absolute continuity
#3718  six-color joint coordinate elimination spine
#3722  retained sigma-algebras as coordinate-data pullbacks
#3726  left retained sigma exact coordinate presentation
#3728  dependence on all six retained supports collapses to opposite boundary
#3732  pair-Haar two-boundary measurability collapses to the mean
#3737  common strong representatives collapse to one boundary
#3740  six-retained AE measurability transported to pair Haar
#3742  shared-base Fubini / six-retained AE descent
#3746  actual twelve-color common-fixed sector = ground-state-a.e. constants
```

The common-fixed-space identification is no longer an open roadmap item.

---

# Phase 9 — Exact twelve-spatial residual-kernel geometry

**Status: Integrated.**

Canonical sequence:

```text
#3768
E12(z)=0
  <-> all twelve conditional expectations fix z
  <-> represented function is ground-state-a.e. constant

#3770
a.e. constant
  <-> equality with an actual constant vector in joint L²

#3773
kernel(E12) = intrinsic real constant line
constant line ∩ constant lineᗮ = {0}

#3775
for physical x in the full top-eigenspace orthogonal sector K,

  E12(R U x)=0 <-> x=0.
```

The #3775 bridge uses the actual transformed positive top vector, the vacuum-`L²` isometry, the right-boundary lift, and injectivity. No rank-one or vacuum-uniqueness assumption is inserted.

### Consequence

The qualitative physical kernel problem is closed.

### Non-consequence

This does **not** prove a positive scale-independent Poincaré coefficient.

---

# Phase 10 — Same-color Wilson plaquette and support separation

**Status: Integrated.**

The next canonical sequence turns the six-color combinatorics into concrete four-dimensional Wilson locality.

```text
#3779
same-colored distinct physical links
  -> cannot share a Wilson plaquette

#3781
same-color separation descends to the actual spatial-slice six-color carrier

#3783
six-color spatial separation
  -> compact plaquette-neighbor exclusion
  -> target-local Wilson action is unchanged by remote same-color replacement
```

This is genuine geometry on the actual Wilson carrier. No probabilistic independence assumption is introduced.

---

# Phase 11 — Exact conditional-law locality and raw heat-bath commutation

**Status: Integrated.**

The geometry is converted into the analytic statement actually needed by the heat-bath operator.

```text
#3787
remote same-color replacement leaves the exact normalized target
single-link Wilson conditional measure unchanged

#3789
same color + distinct spatial links
  -> both conditional-law invariance obligations
  -> compact-product Fubini + commuting replacements
  -> exact raw heat-bath transforms commute
```

The key point is that the proof does not add

```text
h_indep : ...
```

or any equivalent abstract independence hypothesis. The commutation theorem is derived from the actual Wilson geometry and existing conditional measures.

---

# Phase 12 — Six-color bounded-continuous Feller block

**Status: Integrated.**

PR #3791 closes the first parallel-block construction on the actual raw Wilson/Feller side.

Canonical route:

```text
raw six-color heat-bath commutation
  -> bounded-continuous Feller conditional-expectation commutation
  -> fixed-color one-link update family is RightCommutative
  -> List.Perm.foldl_eq
  -> permutation-independent finite fold
  -> canonical fixed six-color parallel Feller heat-bath block
```

Main declarations include the six-spatial fixed-color link subtype, the Feller step, the `RightCommutative` theorem, the permutation-invariant fold theorem, and the canonical block.

### What #3791 does not prove

```text
raw Feller block = ground-state joint Doob block             NOT PROVED
same-color Doob conditional expectations commute             NOT PROVED
six-color ground-state block is an L² orthogonal projection   NOT PROVED HERE
positive block Poincaré coefficient                          NOT PROVED
scale-uniform coercivity                                      NOT PROVED
physical mass gap                                             NOT PROVED
```

This boundary is central to the next phase.

---

# Phase 13 — Present carrier seam: same-color Doob compatibility

**Status: Open now.**

The next theorem unit should connect the newly canonical raw Wilson/Feller same-color locality to the actual vacuum-weighted / ground-state Doob carrier.

The vacuum-weighted one-link law is schematically

```text
μ^Ω_{e,A}(dg) ∝ Ω(A[e <- g]) μ_{e,A}(dg).
```

The raw Wilson result gives control of `μ_{e,A}` under a remote same-color replacement. To obtain same-color Doob commutation, the vacuum factor and normalization must also be transported exactly.

The desired route is

```text
same spatial color + e != f
  -> raw Wilson conditional law at e is invariant under f-resampling
  -> actual vacuum-weighted numerator/normalization compatibility
  -> Doob one-link law at e is invariant under f-resampling
  -> symmetric statement for f
  -> same-color Doob conditional expectations commute
  -> order-independent six-color Doob block
```

### Constraints

```text
no new abstract independence hypothesis
no silent Gibbs/Feller/vacuum-L²/joint-L² identification
no weakening of physical assumptions
no replacement of Ω by a constant unless a theorem justifies it
no use of qualitative common-fixed collapse as a quantitative estimate
```

If the repository already contains the required compatibility under another carrier or notation, add the smallest explicit transport theorem rather than duplicating the analytic layer.

---

# Phase 14 — Quantitative same-color block estimate

**Status: Open next.**

Once the genuine Doob same-color block is available, the next task is a quantitative theorem on that actual carrier.

A useful finite-volume intermediate target is

```text
∃ κ(H,N,beta) > 0,
  κ(H,N,beta) ||x||² <= E12(R U x)
```

for the physical top-orthogonal sector at one finite volume.

A stronger and more useful block formulation could compare

```text
sum of one-link / color-block projection defects
```

against the physical norm on the relevant right-lifted sector.

Valid tools may include

```text
commuting orthogonal projection algebra
conditional-variance decomposition
martingale/block variance identities
comparison of raw Wilson and Doob block forms
block contraction
canonical-path or overlap estimates
```

but every coefficient must be derived explicitly from the actual model.

---

# Phase 15 — Scale-independent twelve-spatial coercivity

**Status: Open after the carrier/block phases.**

The decisive target remains

```text
∃ κ : ℝ,
  0 < κ
  and κ <= 1/2
  and ∀ scale n
  and ∀ x in the physical top-orthogonal sector K_n,

    κ ||x||² <= E12,n(R U x).
```

Equivalently, the proof must upgrade

```text
E12,n(R U x)=0 <-> x=0
```

from qualitative definiteness to one coercive constant that survives the scale family.

### What is now available to attack this

```text
physical kernel triviality
volume-independent one-link Harnack/Doob comparison
exact six-color Wilson geometric separation
exact same-color raw conditional-law locality
exact pairwise raw heat-bath commutation
canonical order-independent six-color Feller block
exact E12 -> physical transfer-gap routing
```

The missing ingredients are the genuine Doob carrier transport and a global quantitative estimate that does not degrade with scale.

### Forbidden shortcuts

Do not infer the target from

```text
trivial kernel at every scale
finite-dimensionality at each scale
mutual absolute continuity alone
local variance positivity alone
pairwise commutation alone
pointwise strict positivity of the vacuum
finite-volume q_n < 1 without a uniform lower bound
```

---

# Phase 16 — Uniform physical transfer gap

**Status: Integrated implication machinery / Open downstream realization.**

Once Phase 15 is proved with a single `κ>0`, the existing canonical theorem gives

```text
physical top-eigenspace transfer gap >= 3κ/4
```

uniformly along the scale family.

This converts the ground-state conditional-expectation geometry into a genuine scale-uniform physical spectral separation.

---

# Phase 17 — Uniform Green, resolvent, and decay control

**Status: Open downstream.**

Use the uniform transfer gap to obtain scale-stable versions of the already-integrated finite-volume structures:

```text
uniform non-top contraction
uniform resolvent exclusion
uniform Green-operator bounds
uniform Euclidean-time decay
uniform relative Poincaré/coercivity
```

Every transport must remain on the correct physical carrier.

---

# Phase 18 — Thermodynamic / scaling-limit physical carrier

**Status: Open downstream.**

Required work includes

```text
construct/control the relevant physical limiting carrier
prove convergence/compatibility of the transfer or semigroup data
transport the uniform spectral lower bound through the limit
retain same-root provenance from the finite Wilson model
```

A scalar observable continuum law is not a substitute for this full physical limit.

---

# Phase 19 — Continuum OS/Wightman physical spectral gap

**Status: Open downstream.**

Target:

```text
actual physical continuum vacuum sector
  + self-adjoint Hamiltonian
  + strictly positive lower spectral bound on vacuum complement.
```

This must be proved on the actual continuum physical carrier, not only through an abstract implication package or one selected mode.

---

# Phase 20 — Clay-level completion

**Status: Open.**

Major obligations remain:

```text
full same-root 4D continuum Yang--Mills field/state
required Euclidean/Wightman axioms and physical identification
correct vacuum structure
strict positive spectrum above vacuum
final existence-and-mass-gap theorem in the Clay sense
```

The repository's policy is to keep these obligations explicit until they are actually closed.

---

# Parallel lane — Global Gibbs `L²` fixed-color projections

**Status: Parallel lane.**

Earlier eight-color work already contains a reusable pattern for lifting bounded-continuous same-color commutation to the genuine Wilson Gibbs `L²` carrier by density and continuity, then building idempotent/self-adjoint fixed-color projection blocks.

That pattern may be useful for the six-spatial-color carrier, but it must not be confused with the ground-state joint Doob `L²` problem. A global Gibbs `L²` block is an intermediate analytic object unless an explicit theorem identifies the relevant ground-state conditional law.

---

# Parallel lane — Exact selected modes / certificates

**Status: Parallel lane / implication machinery.**

The repository also contains exact-mode, spectral-certificate, logarithmic-generator, and point-energy machinery. These results are useful for spectral realization and auditing, but they do not replace the global scale-uniform coercivity theorem.

In particular:

```text
one exact positive mode != proof of the global mass gap
```

unless the global lower spectral bound and carrier identification are separately established.

---

# Immediate next proof units

The recommended order from the current canonical checkpoint is:

```text
1. Inspect actual ground-state/Doob one-link law definitions and existing bridges.

2. Prove the smallest explicit same-color vacuum-weight compatibility theorem:

   same color + e != f
     -> Doob law at e unchanged by f-resampling.

3. Use the existing generic compact heat-bath commutation machinery to prove
   same-color Doob conditional-expectation commutation.

4. Build the genuine order-independent six-color Doob block on the correct
   ground-state carrier.

5. Derive a finite-volume quantitative block/coercivity estimate.

6. Track every coefficient with scale and prove a single positive lower bound
   along the intended scale family.

7. Invoke the already-canonical twelve-spatial -> six-spatial -> transfer-gap
   routing only after the model-derived κ is available.
```

A finite-volume coefficient `κ(H,N,beta)>0` is a useful milestone, but it must remain labeled finite-volume. The decisive promotion step is a uniform lower bound along the intended scale family.

---

# Current checkpoint summary

```text
Authoritative theorem branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Canonical SHA:
  2e294f5c9f95484c42809048cea4d08f284adba2

Latest theorem merge:
  PR #3791

Latest integrated structural result:
  exact six-color raw Wilson heat-bath commutation and an
  order-independent bounded-continuous Feller color block

Immediate open seam:
  explicit same-color ground-state Doob compatibility / commutation

Main quantitative open theorem after that:
  positive scale-independent twelve-spatial Poincaré/coercivity coefficient

Canonical implication after κ:
  physical transfer gap >= 3κ/4

Lean:
  leanprover/lean4:v4.30.0-rc2

Mathlib:
  5450b53e5ddc75d46418fabb605edbf36bd0beb6
```