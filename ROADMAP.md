# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-10 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

and the current authoritative exact canonical theorem SHA is

```text
c0cda8667a3d94eb2576ac602a93943980c9c0c3
```

which is the normal merge commit of PR #3798,

```text
Add ground-state joint one-link conditional expectation geometry.
```

Post-merge validation:

```text
PR Lean Fast Check #13502 = completed / success.
```

The public `main` branch is a landing/documentation surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status.

> **Current frontier**
>
> The qualitative twelve-spatial kernel obstruction is closed. The same-color raw Wilson locality/heat-bath chain is formalized. The remote-replacement Doob law has been reduced to an explicit vacuum-weight normal form. Most recently, a genuine one-link conditional expectation has been constructed directly on the ground-state joint `L²` carrier, with one-link residual bounded above by the containing six-color residual.
>
> Therefore the next proof unit should attack the **actual ground-state joint one-link conditional law / disintegration** and connect it quantitatively to the physical one-link Doob fiber. The subsequent global step must avoid an inverse-volume loss when passing from one-link information to color/twelve-spatial coercivity.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative theorem carrier.
- **Integrated implication machinery** — downstream implication is formalized, but a model-facing quantitative input remains.
- **Open now** — immediate constructive frontier.
- **Open next** — follows directly after the current seam.
- **Open downstream** — required after the present quantitative frontier.
- **Parallel route** — mathematically useful but not logically required for the main path.
- **Diagnostic only** — correct information that must not be mistaken for the missing theorem.

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

D. LOCAL PHYSICAL DOOB CONTROL

continuous positive physical vacuum                                 [Integrated]
  -> volume-independent one-link Harnack factor exp(8 beta)          [Integrated]
  -> physical Doob one-link conditional law                          [Integrated]
  -> centered one-link resampling gap = 1                            [Integrated]
  -> exp(-16 beta) variance comparison                               [Integrated]
  -> native Wilson one-link variance / projection-defect bridge      [Integrated]

E. GROUND-STATE TWELVE-SPATIAL GEOMETRY

one-slab ground-state joint probability law                          [Integrated]
  -> 6 right + 6 left genuine spatial condExp projections            [Integrated]
  -> common fixed by all 12 = a.e. constants                        [Integrated: #3746]
  -> kernel(E12) = intrinsic constant line                           [Integrated: #3773]
  -> E12(RUx)=0 <-> x=0 on physical K                               [Integrated: #3775]

F. SAME-COLOR WILSON / RAW HEAT-BATH

same-color physical plaquette separation                             [Integrated: #3779]
  -> six-spatial-color separation                                   [Integrated: #3781]
  -> compact Wilson local-action separation                         [Integrated: #3783]
  -> exact raw conditional-law locality                             [Integrated: #3787]
  -> exact same-color raw heat-bath commutation                     [Integrated: #3789]
  -> order-independent fixed-color raw/Feller block                 [Integrated: #3791]

G. DOOB REMOTE-REPLACEMENT NORMAL FORM

raw same-color locality
  -> after remote replacement, target Doob law uses
     the same raw target measure + explicit two-link Ω weight        [Integrated: #3795]

remaining Doob locality obstruction
  = vacuum-weight compatibility                                      [Open / optional route]

H. GENUINE JOINT ONE-LINK CONDITIONAL EXPECTATION

full left boundary + right off-target sigma algebra                  [Integrated: #3798]
  -> genuine joint one-link condExpL2                                [Integrated: #3798]
  -> off-color sigma algebra <= off-target sigma algebra             [Integrated: #3798]
  -> one-link residual <= containing color residual                  [Integrated: #3798]

I. IMMEDIATE CARRIER / DISINTEGRATION SEAM

actual ground-state joint one-link conditional distribution
  <-> physical one-link Doob fiber                                   [OPEN NOW]

acceptable result:
  exact identity
or
  explicit quantitative comparison with scale-independent constants

then

physical one-link variance
  -> genuine joint one-link residual
  -> containing six-color residual                                  [OPEN NEXT]

J. BLOCK / GLOBAL QUANTITATIVE SEAM

one-link information
  -> color/twelve-spatial estimate without 1/(number of links) loss [OPEN NEXT]

possible mechanisms:
  block Poincaré
  approximate tensorization
  martingale variance decomposition
  block conditional-expectation comparison
  canonical-path/frame estimate
  another rigorous uniform mixing theorem

K. SCALE-UNIFORM TARGET

∃ κ > 0, independent of scale n,
  ∀ n, ∀ x ∈ K_n,

  κ ||x||² <= E12,n(R U x)                                           [OPEN NOW AFTER I/J]

  -> six-spatial frame coefficient 2κ                               [Integrated implication machinery]
  -> physical transfer gap >= 3κ/4                                 [Integrated implication machinery]
  -> scale-uniform positive physical transfer gap                   [OPEN DOWNSTREAM]

L. THERMODYNAMIC / CONTINUUM PHYSICAL PROPAGATION

uniform physical transfer gap                                       [OPEN DOWNSTREAM]
  -> stable Green / resolvent / decay bounds                         [OPEN DOWNSTREAM]
  -> controlled thermodynamic/scaling limit                          [OPEN DOWNSTREAM]
  -> physical OS/Wightman/Hamiltonian spectral lower bound           [OPEN DOWNSTREAM]

M. CLAY-LEVEL COMPLETION

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

Pinned environment:

```text
Lean    leanprover/lean4:v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

Permanent logical boundaries:

```text
finite-volume theorem != continuum theorem
trivial kernel != quantitative coercivity
q_n < 1 for all n != inf_n(1-q_n)>0
mutual absolute continuity != uniform L² norm equivalence
raw Wilson locality != vacuum-weighted Doob locality without transport
one-link residual <= color residual != tensorization over all links
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

The root is the actual periodic-even compact special-unitary Wilson Gibbs model. Integrated components include oriented lattice/edge/plaquette geometry, normalized Haar probability, Wilson action/Gibbs measure, reflection positivity, boundary and spatial-slice carriers, gauge-covariant holonomy, gauge-invariant observables, one-slab Wilson kernels, and physical transfer operators.

**Permanent rule:** keep the interacting Wilson model visible through every decisive physical bridge. Do not replace it by product Haar or an abstract projection system unless an explicit theorem justifies that transport.

---

# Phase 2 — Same-root primary scalar continuum law

**Status: Integrated.**

```text
finite gauge-invariant scalar readout
  -> rational-time path law
  -> tight finite pushforward family
  -> subsequential continuum probability law
  -> continuum scalar reflection positivity
```

This is a same-root continuum observable process, not yet the complete gauge field on `ℝ⁴`.

---

# Phase 3 — Continuum OS Hilbert reconstruction and Hamiltonian

**Status: Integrated.**

The canonical lane contains the OS null quotient, fixed-slot real Hilbert completions, directed-limit Hilbert carrier, real strongly continuous contraction semigroup, graph-closed self-adjoint Hamiltonian, normalized vacuum, and complete vacuum-orthogonal sector.

This lane is important downstream but is not the current quantitative bottleneck.

---

# Phase 4 — Finite physical transfer and pair geometry

**Status: Integrated.**

Let schematically

```text
F  = full eigenvalue-one subspace
K  = Fᗮ
PP = completed physical pair carrier
TT = top-top block
NN = non-top block
R  = normalized one-slice restriction
q  = ||R||.
```

The canonical branch contains `PP = TT ⊕ NN`, strict fixed-volume `q < 1`, non-top power decay, strong convergence, coercivity/spectral exclusion, resolvent bounds, Green operators, exact reduced ranges, and relative finite-volume Poincaré estimates.

**Non-consequence:** fixed-volume strict contraction does not provide a scale-uniform gap.

---

# Phase 5 — Continuous-vacuum Harnack and physical one-link Doob control

**Status: Integrated.**

The model-facing local route contains

```text
one-link Wilson action oscillation bound
  -> one-slab kernel ratio <= exp(8 beta)
  -> continuous-vacuum Harnack control
  -> physical Doob one-link conditional probability law
  -> centered one-link resampling residual = conditional variance
  -> one-link resampling gap = 1
  -> raw Wilson variance * exp(-16 beta)
       <= physical Doob variance.
```

A native Wilson conditional-variance / Gibbs `L²` projection-defect bridge also exists.

**Important boundary:** these are one-link theorems. They do not yet identify the physical Doob fiber with the conditional distribution inside the ground-state joint one-slab law.

---

# Phase 6 — Genuine twelve-spatial conditional expectations

**Status: Integrated.**

On the actual ground-state joint `L²` carrier there are six right and six left spatial conditional expectations. The conventional twelve-spatial residual satisfies the right-lift relation required by the downstream frame/gap machinery.

The implication

```text
12-spatial Poincaré κ
  -> six-spatial frame coefficient 2κ
  -> physical transfer gap >= 3κ/4
```

is already formalized. The missing object is the model-derived uniform `κ`.

---

# Phase 7 — Common-fixed collapse and exact residual kernel

**Status: Integrated.**

Canonical milestones:

```text
#3746  actual twelve-color common-fixed sector = ground-state-a.e. constants
#3768  E12(z)=0 iff represented function is ground-state-a.e. constant
#3770  a.e. constant iff equality with an actual constant vector
#3773  kernel(E12) = intrinsic real constant line
#3775  E12(R U x)=0 iff x=0 on the genuine physical full-top-orthogonal sector
```

The qualitative kernel problem is therefore closed.

**Permanent warning:** injectivity is not a positive uniform coercivity constant.

---

# Phase 8 — Same-color Wilson locality and raw block dynamics

**Status: Integrated.**

```text
#3779  same-colored distinct physical links cannot share a Wilson plaquette
#3781  separation descends to the actual six spatial color classes
#3783  compact Wilson target-local action is unchanged by a remote same-color replacement
#3787  exact normalized raw target one-link conditional measure is unchanged
#3789  exact same-color raw heat-bath transforms commute
#3791  bounded-continuous Feller commutation + permutation-independent fixed-color block
```

This entire route is derived from the actual compact Wilson geometry. No abstract independence axiom is added.

---

# Phase 9 — Doob remote-replacement normal form

**Status: Integrated: PR #3795.**

PR #3795 isolates the precise difference between raw Wilson locality and physical Doob locality. For distinct links, once raw target-law invariance is known, the remotely updated target Doob law can be rewritten using the **original raw target measure** together with the two-link weight

```text
Ω(A[e <- g][f <- v]).
```

Thus the raw Wilson part of the seam is eliminated. Any further same-color Doob locality theorem must prove a property of the vacuum weight, or use a weaker quantitative comparison sufficient for the final estimate.

### Roadmap consequence

Same-color Doob commutation remains a valid **parallel route**, but is no longer treated as a mandatory prerequisite for all progress toward coercivity.

---

# Phase 10 — Genuine joint one-link conditional expectation

**Status: Integrated: PR #3798.**

For a target right-boundary spatial link, PR #3798 defines the sigma algebra retaining

```text
complete left boundary
+ every right-boundary spatial coordinate except the target.
```

It constructs the genuine one-link `condExpL2` projection directly on the existing ground-state joint law.

The off-six-color sigma algebra is proved to be contained in the off-target sigma algebra. Mathlib orthogonal-projection geometry then gives

```text
||f - P_target f|| <= ||f - P_color(target) f||
```

and the corresponding squared-energy inequality.

### Why this matters

Any future lower bound on the genuine one-link residual immediately lower-bounds the containing color residual. This provides a direct local-to-color route that does **not** require proving same-color Doob commutation first.

### What it does not solve

For many links in one color, individual inequalities cannot be naively summed without a possible volume-dependent factor. A uniform block/global theorem is still required.

---

# Phase 11 — Immediate next theorem: ground-state joint one-link disintegration

**Status: Open now. Highest priority.**

The next proof unit should inspect the exact density of the ground-state one-slab joint measure and derive its conditional law when all coordinates except one target right-boundary spatial link are fixed.

Preferred target:

```text
conditional law of target link under Π_ground-state
  = physical one-link Doob conditional law
```

if the exact definitions support equality.

If exact equality is not definitionally or mathematically available, prove instead a quantitative two-sided comparison with explicit constants derived from the actual kernel/vacuum structure.

The proof must remain same-root and carrier explicit. No new statement of independence or unexplained measure identification is acceptable.

### Expected ingredients to inspect

```text
ground-state joint density
one-slab physical kernel factorization in the target link
strictly-positive vacuum factors
normalized one-link Wilson conditional measure
singleLinkDoobConditionalMeasure
Radon--Nikodym / disintegration normalization
existing local Harnack bounds
```

---

# Phase 12 — One-link variance to genuine joint residual

**Status: Open next.**

Once Phase 11 is closed, formalize the integrated conditional-variance identity/comparison

```text
physical Doob one-link variance
  -> ground-state joint conditional variance
  = ||f - P_target f||².
```

Then combine with PR #3798:

```text
joint one-link residual²
  <= containing six-color residual².
```

This is the cleanest currently visible carrier-safe route from the existing local Harnack/Doob estimates into the genuine twelve-spatial energy.

---

# Phase 13 — Uniform block/global estimate

**Status: Open next and mathematically decisive.**

A color contains a scale-dependent number of links. Therefore

```text
E_color >= E_target
```

for each target does **not** justify

```text
E_color >= sum_target E_target
```

with a scale-independent coefficient.

The next global theorem must prevent this loss. Candidate mechanisms include:

```text
block Poincaré inequality
exact or approximate tensorization within a color
martingale/Efron--Stein variance decomposition
uniform comparison between block and one-link conditional expectations
Dobrushin-type contraction with explicit volume-independent constant
canonical paths / frame estimate
another same-root block-dynamics estimate
```

The route should be chosen by what the actual Wilson/Doob ground-state measure proves, not by inserting a generic assumption merely sufficient for the desired conclusion.

---

# Phase 14 — Scale-independent twelve-spatial coercivity

**Status: Open central target.**

Prove

```text
∃ κ > 0,
  ∀ scale n,
  ∀ x ∈ K_n,

  κ ||x||² <= E12,n(R U x).
```

The coefficient `κ` must be independent of scale. A positive coefficient constructed separately for each finite volume is insufficient.

Once this theorem is available, the already-integrated implication machinery yields

```text
six-spatial coefficient = 2κ
physical transfer gap >= 3κ/4.
```

---

# Phase 15 — Thermodynamic/scaling propagation

**Status: Open downstream.**

A uniform finite-volume physical transfer gap should then be propagated through stable resolvent/Green/decay estimates and a controlled thermodynamic/scaling limit. The carrier and normalization must remain explicitly connected to the same-root physical construction.

---

# Phase 16 — Full continuum physical completion

**Status: Open downstream.**

Remaining obligations include a full same-root four-dimensional continuum gauge field/state, the required physical OS/Wightman identification, correct vacuum structure, and a strictly positive continuum spectral lower bound above the vacuum.

Only after those steps may the repository claim a Clay-level Yang--Mills existence and mass-gap result.

---

# Current next-action order

```text
1. Inspect exact ground-state joint density and target-link factorization.
2. Prove exact or quantitative target-link conditional-distribution bridge to physical Doob law.
3. Convert that bridge into a genuine joint one-link conditional-variance theorem.
4. Feed it through #3798 one-link <= color residual monotonicity.
5. Prove a block/global estimate that avoids inverse-volume loss.
6. Produce scale-independent κ for E12 on physical K_n.
7. Invoke existing 2κ / 3κ/4 downstream transfer-gap machinery.
8. Only then attack thermodynamic/scaling and continuum physical propagation.
```

Parallel work on explicit vacuum-weight compatibility and same-color Doob commutation remains useful if it yields the uniform block estimate more efficiently, but it should not be treated as logically mandatory when the direct joint-one-link route suffices.

---

## Canonical checkpoint represented by this roadmap

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Canonical theorem SHA:
  c0cda8667a3d94eb2576ac602a93943980c9c0c3

Latest theorem PR:
  #3798 Add ground-state joint one-link conditional expectation geometry

Post-merge CI:
  PR Lean Fast Check #13502 = completed / success

Pinned Lean:
  leanprover/lean4:v4.30.0-rc2

Pinned mathlib:
  5450b53e5ddc75d46418fabb605edbf36bd0beb6
```
