# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-10 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The current authoritative exact canonical SHA is

```text
f82275f25c7e33de1410ec1e58b3533097d9383b
```

which is the normal merge commit of PR #3775,

```text
Close twelve-spatial kernel on physical top-orthogonal sector.
```

Its merge-push validation is

```text
PR Lean Fast Check #13476 = completed / success.
```

The public `main` branch is a landing/documentation surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status.

> **Current frontier**
>
> The qualitative ground-state twelve-color problem is now closed at the level needed for the next quantitative step. The genuine twelve-spatial common-fixed sector is identified with constants; zero twelve-spatial residual is identified with the intrinsic constant line in the actual joint `L²`; and on the genuine physical full-top-orthogonal sector the residual vanishes only at zero.
>
> The immediate unresolved theorem is therefore a **positive scale-independent `L²` Poincaré/coercivity estimate** for the actual twelve-spatial ground-state conditional-expectation dynamics on the physical right-boundary top-orthogonal sector.
>
> Once such a `κ>0` is proved, the canonical routing already gives a physical transfer-gap lower bound `3κ/4`.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative theorem carrier.
- **Integrated implication machinery** — downstream implication is formalized, but a model-facing quantitative input remains.
- **Open now** — immediate constructive frontier.
- **Open downstream** — required after the present frontier.
- **Parallel lane** — useful but not the main current obstruction.
- **Diagnostic only** — mathematically correct information that must not be mistaken for the missing quantitative theorem.

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
  -> left/right boundary L² isometries                               [Integrated]
  -> 6 right genuine spatial condExp projections                     [Integrated]
  -> 6 left genuine spatial condExp projections                      [Integrated]
  -> genuine 12-spatial family on one joint L² carrier               [Integrated]
  -> retained-coordinate elimination                                [Integrated]
  -> joint/pair-Haar null-set equivalence                            [Integrated]
  -> pair-Haar AE descent and two-boundary collapse                  [Integrated]
  -> common fixed by all 12 = a.e. constants                        [Integrated: #3746]

F. TWELVE-SPATIAL RESIDUAL KERNEL

E12(z)=0 <-> fixed by all 12                                         [Integrated]
  -> E12(z)=0 <-> ground-state-a.e. constant                         [Integrated: #3768]
  -> a.e. constant <-> actual constant vector in joint L²            [Integrated: #3770]
  -> kernel = intrinsic real constant line                           [Integrated: #3773]
  -> kernel ∩ constant-lineᗮ = {0}                                   [Integrated: #3773]
  -> on physical full-top-orthogonal sector, E12(RUx)=0 <-> x=0      [Integrated: #3775]

G. PRESENT QUANTITATIVE FRONTIER

prove one κ > 0 independent of scale with

  κ ||x||² <= E12,n(R U x)

for every scale n and x in physical K_n                              [OPEN NOW]
  using actual Wilson / Doob / Harnack / condExp geometry             [OPEN NOW]

then

  uniform 12-spatial Poincaré κ
    -> uniform six-spatial frame 2κ                                  [Integrated implication machinery]
    -> physical transfer gap >= 3κ/4                                 [Integrated implication machinery]
    -> scale-uniform positive physical transfer gap                  [OPEN DOWNSTREAM]

H. THERMODYNAMIC / CONTINUUM PHYSICAL PROPAGATION

uniform physical transfer gap                                       [OPEN DOWNSTREAM]
  -> stable Green / resolvent / decay bounds                         [OPEN DOWNSTREAM]
  -> controlled physical thermodynamic/scaling limit                 [OPEN DOWNSTREAM]
  -> physical OS/Wightman/Hamiltonian spectral lower bound           [OPEN DOWNSTREAM]

I. CLAY-LEVEL COMPLETION

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

This is downstream infrastructure. The active proof program is upstream: derive a scale-uniform quantitative constant from the actual ground-state Wilson dynamics.

---

# Phase 6 — Continuous-vacuum local Harnack and one-link coercivity

**Status: Integrated.**

The local model-facing route now contains

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

### Remaining issue

The local constant is explicit and volume-independent, but a theorem is still needed to assemble local control into the required global twelve-block Poincaré inequality without scale degradation.

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

This already yields the implication

```text
12-spatial Poincaré κ
  -> six-spatial frame 2κ
  -> physical transfer gap >= 3κ/4.
```

The implication is integrated; production of a uniform `κ` is not.

---

# Phase 8 — Six-color retained-coordinate elimination

**Status: Integrated.**

The old qualitative obstruction has been discharged through a sequence of explicit finite-coordinate and measure-theoretic theorems.

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

### Completed conclusion

The common-fixed-space identification is no longer an open roadmap item.

---

# Phase 9 — Exact twelve-spatial residual-kernel geometry

**Status: Integrated.**

Recent canonical sequence:

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

# Phase 10 — The present quantitative theorem

**Status: Open now.**

The target is the actual scale-family statement already exposed by the canonical routing:

```text
∃ κ : ℝ,
  0 < κ
  and κ <= 1/2
  and ∀ scale n
  and ∀ x in the physical top-orthogonal sector K_n,

    κ ||x||² <= E12,n(R U x).
```

Equivalently, the next proof must upgrade

```text
E12,n(R U x)=0 <-> x=0
```

from qualitative definiteness to one coercive constant that survives the scale family.

### Required mathematical content

A valid proof will need a quantitative mechanism such as a genuine block-dynamics contraction, martingale/variance decomposition, comparison theorem, canonical-path estimate, spectral argument, or another rigorous global mixing/coercivity device derived from the actual Wilson/Doob structure.

The existing local Harnack factor `exp(-16 beta)` is an ingredient, not by itself the global theorem.

### Forbidden shortcuts

Do not infer the target from

```text
trivial kernel at every scale
finite-dimensionality at each scale
mutual absolute continuity alone
local variance positivity alone
pointwise strict positivity of the vacuum
finite-volume q_n < 1 without a uniform lower bound
```

---

# Phase 11 — Uniform physical transfer gap

**Status: Integrated implication machinery / Open downstream realization.**

Once Phase 10 is proved with a single `κ>0`, the existing canonical theorem gives

```text
physical top-eigenspace transfer gap >= 3κ/4
```

uniformly along the scale family.

This is the next major milestone because it converts the local/joint conditional-expectation geometry into a genuine scale-uniform physical spectral separation.

---

# Phase 12 — Uniform Green, resolvent, and decay control

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

# Phase 13 — Thermodynamic / scaling-limit physical carrier

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

# Phase 14 — Continuum OS/Wightman physical spectral gap

**Status: Open downstream.**

Target:

```text
actual physical continuum vacuum sector
  + self-adjoint Hamiltonian
  + strictly positive lower spectral bound on vacuum complement.
```

This must be proved on the actual continuum physical carrier, not only through an abstract implication package or one selected mode.

---

# Phase 15 — Clay-level completion

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

# Parallel lane — Exact selected modes / certificates

**Status: Parallel lane / implication machinery.**

The repository also contains exact-mode, spectral-certificate, logarithmic-generator, and point-energy machinery. These results are useful for spectral realization and auditing, but they do not replace the global scale-uniform coercivity theorem of Phase 10.

In particular:

```text
one exact positive mode != proof of the global mass gap
```

unless the global lower spectral bound and carrier identification are separately established.

---

# Immediate next proof unit

The next theorem unit should remain tightly focused on the quantitative frontier:

```text
INPUTS ALREADY CANONICAL

actual ground-state joint measure
actual twelve spatial conditional expectations
common fixed = constants
kernel(E12) = constant line
physical top-orthogonal kernel triviality
local volume-independent Harnack/Doob one-link comparison
exact E12 -> physical transfer-gap routing

NEXT OUTPUT

one genuinely derived coercive lower bound for E12 on physical right lifts,
preferably in a form that makes scale dependence explicit and can then be
strengthened to a single scale-independent κ.
```

If an intermediate theorem only gives a finite-volume coefficient `κ(H,N,beta)>0`, it is still useful, but it must be labeled finite-volume. The decisive promotion step is a uniform lower bound along the intended scale family.

---

# Current checkpoint summary

```text
Authoritative theorem branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Canonical SHA:
  f82275f25c7e33de1410ec1e58b3533097d9383b

Latest theorem merge:
  PR #3775

Latest theorem statement reached:
  on the genuine physical full-top-orthogonal sector,
  twelve-spatial residual energy vanishes iff the vector is zero

Main open theorem:
  positive scale-independent twelve-spatial Poincaré/coercivity coefficient

Canonical implication after that:
  transfer gap >= 3κ/4

Lean:
  leanprover/lean4:v4.30.0-rc2

Mathlib:
  5450b53e5ddc75d46418fabb605edbf36bd0beb6
```
