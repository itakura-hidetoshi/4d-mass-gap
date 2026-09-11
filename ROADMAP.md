# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-11 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

and the current authoritative exact canonical theorem SHA is

```text
f65c0fc75c56ffdcba103331768b8aa73fbfba65
```

which is the normal merge commit of PR #3880,

```text
Bound one-slab right target local Boltzmann factor.
```

Validated exact theorem head:

```text
6f33df5b7d7f1c4258101b55a7d1372edfb15680
```

Validation:

```text
PR Lean Fast Check #13579 = completed / success.
```

The public `main` branch is a landing/documentation surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status.

> **Current frontier**
>
> The former one-link disintegration seam has been substantially closed at the explicit fiber/measure level. The repository now has target/off-target Haar splitting, a.e. finite-positive target fibers, normalized target probability fibers, a measurable Markov-kernel representative with exact global integral identity, transport back to original right-boundary coordinates, direct `SU(N)` target-coordinate bridges, and direct ground-state one-link weight factorization.
>
> The latest chain then localizes a literal right-target update of the one-slab Wilson kernel and proves the volume-independent factor bound
>
> ```text
> exp(-8 beta) <= localFactor <= exp(8 beta).
> ```
>
> Therefore the highest-priority next unit is no longer “construct the one-link disintegration.” It is to **normalize the target-local factor inside the actual ground-state one-link fiber and obtain an explicit volume-independent normalized comparison / minorization theorem**. After that, the problem is to convert the one-link estimate into genuine joint conditional-variance control and globalize it to six-color / twelve-spatial coercivity without inverse-volume loss.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative theorem carrier.
- **Integrated implication machinery** — downstream implication is formalized, but a model-facing quantitative input remains.
- **Open now** — immediate constructive frontier.
- **Open next** — directly follows the current seam.
- **Open downstream** — required after the present quantitative frontier.
- **Parallel route** — mathematically useful but not mandatory for the main path.
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
  -> Hilbert carrier / real C0 semigroup                             [Integrated]
  -> graph-closed self-adjoint Hamiltonian                           [Integrated]
  -> vacuum Omega / complete Omega-perp                              [Integrated]

C. FINITE PHYSICAL TRANSFER / PAIR THEORY

full top eigenspace F and K = F-perp                                 [Integrated]
  -> completed TT / NN decomposition inside PP                       [Integrated]
  -> fixed-volume strict non-top contraction                         [Integrated]
  -> decay / strong convergence / resolvent / Green                  [Integrated]
  -> finite-volume relative Poincare                                 [Integrated]

D. LOCAL PHYSICAL DOOB CONTROL

continuous positive physical vacuum                                  [Integrated]
  -> volume-independent local Harnack control                        [Integrated]
  -> physical one-link Doob law                                      [Integrated]
  -> centered one-link resampling gap = 1                            [Integrated]
  -> explicit local variance comparison                              [Integrated]

E. GROUND-STATE TWELVE-SPATIAL GEOMETRY

one-slab ground-state joint probability law                          [Integrated]
  -> 6 right + 6 left genuine spatial condExp projections            [Integrated]
  -> common fixed by all 12 = a.e. constants                         [Integrated]
  -> kernel(E12) = intrinsic constant line                           [Integrated]
  -> E12(RUx)=0 <-> x=0 on physical K                               [Integrated]

F. SAME-COLOR RAW WILSON BLOCK

same-color plaquette / action locality                               [Integrated]
  -> exact raw one-link conditional-law locality                     [Integrated]
  -> exact same-color raw heat-bath commutation                      [Integrated]
  -> permutation-independent fixed-color Feller block                [Integrated]
  -> remote-replacement Doob normal form                             [Integrated]

G. GENUINE JOINT ONE-LINK CONDEXP

off-target sigma algebra                                             [Integrated]
  -> genuine joint target condExpL2                                  [Integrated]
  -> off-color sigma <= off-target sigma                             [Integrated]
  -> target residual <= containing color residual                    [Integrated]

H. GROUND-STATE ONE-LINK FIBER / MARKOV LAYER

literal target fiber measure                                         [Integrated]
  -> target/off-target Haar split                                    [Integrated]
  -> a.e. measurable target sections                                [Integrated]
  -> a.e. 0 < fiberMass < infinity                                  [Integrated]
  -> normalized a.e. probability fibers                             [Integrated]
  -> exact fiber normalization identity                             [Integrated]
  -> measurable normalized Markov-kernel representative             [Integrated]
  -> exact global lintegral identity                                [Integrated]
  -> ground-state split specialization                              [Integrated]
  -> original-coordinate Markov identity                            [Integrated]
  -> singleton target <-> direct SU(N) coordinate bridge            [Integrated]
  -> normalized split fiber -> direct target coordinate             [Integrated]

I. DIRECT GROUND-STATE ONE-LINK WEIGHT

direct one-link fiber density                                        [Integrated]
  -> left vacuum * literal one-slab Wilson kernel * right vacuum     [Integrated]

J. TARGET-LOCAL ONE-SLAB FACTORIZATION

right target update of one-slab action                              [Integrated]
  -> crossing target-link localization                              [Integrated]
  -> spatial target-link localization                               [Integrated]
  -> complete target-local action variation                         [Integrated]
  -> exact division-free kernel multiplier                          [Integrated]
  -> named local Boltzmann factor                                   [Integrated]
  -> exp(-8 beta) <= localFactor <= exp(8 beta)                     [Integrated: #3880]

K. NORMALIZED TARGET-FIBER COMPARISON

unnormalized local factor bounds
  -> normalization denominator bounds                               [OPEN NOW]
  -> explicit normalized one-link density ratio bounds              [OPEN NOW]
  -> volume-independent minorization / Harnack comparison           [OPEN NOW]

L. GENUINE JOINT ONE-LINK QUANTITATIVE CONTROL

normalized target-fiber comparison
  -> lower bound on genuine target conditional variance             [OPEN NEXT]
  -> lower bound on target projection defect                         [OPEN NEXT]
  -> containing six-color residual receives same local information  [OPEN NEXT]

M. BLOCK / GLOBAL QUANTITATIVE SEAM

one-link information
  -> color/twelve-spatial estimate without 1/(number of links) loss [OPEN NEXT]

N. SCALE-UNIFORM TARGET

there exists kappa > 0, independent of n,
  for every n and every x in K_n,

  kappa ||x||^2 <= E12,n(R U x)                                      [OPEN]

  -> six-spatial frame coefficient 2 kappa                           [Integrated implication machinery]
  -> physical transfer gap >= 3 kappa / 4                            [Integrated implication machinery]

O. THERMODYNAMIC / CONTINUUM PHYSICAL PROPAGATION

uniform physical transfer gap                                       [OPEN DOWNSTREAM]
  -> stable Green / resolvent / decay bounds                         [OPEN DOWNSTREAM]
  -> controlled thermodynamic/scaling limit                          [OPEN DOWNSTREAM]
  -> physical OS/Wightman/Hamiltonian spectral lower bound           [OPEN DOWNSTREAM]

P. CLAY-LEVEL COMPLETION

full same-root 4D continuum gauge field/state                        [OPEN]
correct vacuum structure                                             [OPEN]
full physical OS/Wightman identification                             [OPEN]
strictly positive continuum spectrum above vacuum                    [OPEN]
Clay-level existence + mass gap                                      [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository-operation rules for theorem work:

```text
start from the exact authoritative canonical SHA
use the theorem carrier, not public main, for theorem status
accept CI only at terminal success
never treat queued/in_progress as success
write-freeze while exact-head CI is running
inspect the first genuine Lean error before editing a failed head
keep theorem development additive / tighten-only
never weaken physical assumptions silently
never identify unrelated carriers silently
forbid sorry / admit / new axiom / placeholder theorem declarations
fresh-check exact head / base / mergeability / reviews / threads before merge
normal-merge with expected head SHA fixed
verify merge parents and theorem-branch pointer after merge
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
mutual absolute continuity != uniform L2 norm equivalence
raw Wilson locality != vacuum-weighted Doob locality without transport
measurable normalized fiber != RCD unless proved
unnormalized factor bound != normalized minorization without denominator control
one-link residual <= color residual != tensorization over all links
pairwise commutation != Poincare lower bound
local Harnack/TV comparison != global Poincare without a theorem
selected vacuum vector != full top eigenspace
one exact mode != global spectral floor
same-root scalar continuum != full 4D Yang--Mills field
green open PR != merged canonical theorem
```

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The root is the actual periodic-even compact special-unitary Wilson Gibbs model. Integrated components include oriented lattice/edge/plaquette geometry, normalized Haar probability, Wilson action/Gibbs measure, reflection positivity, boundary and spatial-slice carriers, gauge-covariant holonomy, gauge-invariant observables, one-slab Wilson kernels, and physical transfer operators.

**Permanent rule:** keep the interacting Wilson model visible through every decisive physical bridge. Do not replace it by product Haar or an abstract projection system unless an explicit theorem supplies that transport.

---

# Phase 2 — Same-root continuum scalar OS construction

**Status: Integrated.**

The canonical lane contains finite gauge-invariant scalar readout, rational-time path laws, tight finite pushforward families, subsequential continuum probability laws, continuum reflection positivity, OS quotient/completion, real strongly continuous contraction semigroup, graph-closed self-adjoint Hamiltonian, normalized vacuum, and complete vacuum-orthogonal sector.

This is a same-root continuum scalar observable process, not yet the complete continuum gauge field on `R^4`.

---

# Phase 3 — Finite physical transfer and pair geometry

**Status: Integrated.**

At fixed volume the canonical branch contains the full top eigenspace, its orthogonal complement, the completed physical pair decomposition, strict non-top contraction, power decay, strong convergence, coercivity/spectral exclusion, resolvent bounds, Green operators, exact reduced ranges, and relative finite-volume Poincare estimates.

**Non-consequence:** fixed-volume strict contraction does not provide a scale-uniform gap.

---

# Phase 4 — Local physical Doob / Harnack control

**Status: Integrated.**

The local physical route already contains a one-link Wilson action oscillation bound, volume-independent Harnack control, physical one-link Doob laws, one-link resampling gap `1`, and explicit one-link variance comparisons.

**Boundary:** these local theorems are not yet the desired global Poincare inequality.

---

# Phase 5 — Genuine twelve-spatial conditional-expectation geometry

**Status: Integrated.**

The actual ground-state joint `L2` carrier supports six right and six left spatial conditional expectations. The downstream implication

```text
12-spatial Poincare kappa
  -> six-spatial frame coefficient 2 kappa
  -> physical transfer gap >= 3 kappa / 4
```

is already formalized.

The missing object remains a model-derived scale-uniform `kappa`.

---

# Phase 6 — Qualitative kernel closure

**Status: Integrated.**

Canonical milestones:

```text
#3746  twelve-color common-fixed sector = ground-state-a.e. constants
#3768  E12(z)=0 iff represented function is ground-state-a.e. constant
#3770  a.e. constant iff equality with an actual constant vector
#3773  kernel(E12) = intrinsic real constant line
#3775  E12(RUx)=0 iff x=0 on the genuine physical full-top-orthogonal sector
```

The qualitative kernel problem is closed.

**Permanent warning:** injectivity is not a positive uniform coercivity constant.

---

# Phase 7 — Same-color Wilson locality and raw block dynamics

**Status: Integrated.**

```text
#3779  same-colored distinct physical links cannot share a Wilson plaquette
#3781  separation descends to actual six spatial color classes
#3783  compact Wilson target-local action is unchanged by remote same-color replacement
#3787  exact normalized raw target one-link conditional law is unchanged
#3789  exact same-color raw heat-bath transforms commute
#3791  bounded-continuous Feller commutation + permutation-independent fixed-color block
#3795  exact remote-replacement normal form for the Doob one-link law
```

This route is model-derived. No abstract independence axiom is introduced.

Same-color Doob commutation remains a useful **parallel route**, but it is not the only path to quantitative progress.

---

# Phase 8 — Genuine joint one-link conditional expectation

**Status: Integrated: PR #3798.**

For a target right-boundary spatial link, the canonical layer defines the sigma algebra retaining the complete left boundary and all right-boundary spatial coordinates except the target. It constructs the genuine one-link `condExpL2` directly on the ground-state joint law and proves

```text
||f - P_target f|| <= ||f - P_color(target) f||.
```

Thus a future one-link lower bound can feed the containing color residual directly.

---

# Phase 9 — Explicit ground-state one-link fiber

**Status: Integrated.**

The one-link fiber layer now contains:

```text
#3807  literal target fiber measure and mass
#3810  normalization under explicit fixed-context receipts
#3812  target/off-target Haar split
#3815  a.e. target-fiber measurability
#3820  a.e. positive finite fiber mass
#3823  normalized a.e. probability fibers
#3825  exact normalization identity
```

This replaced the old abstract “we need a fiber model” frontier with a concrete same-root target-fiber construction.

---

# Phase 10 — Measurable Markov representative and exact global identity

**Status: Integrated.**

The generic normalized-weight layer and its ground-state specialization contain:

```text
#3832  measurable normalized Markov-kernel representative
       + exact global lintegral identity
#3840  joint AE measurability after target/off-target split
#3842  product-a.e. finite-positive fiber mass
#3845  measurable Markov disintegration specialized to ground-state split
#3848  split-context Haar coordinate equivalence
#3850  original complete-right coordinate Markov identity
```

**Claim boundary:** this layer is not silently promoted to an RCD statement unless that exact identification is separately formalized.

---

# Phase 11 — Direct `SU(N)` target coordinate and density bridge

**Status: Integrated.**

```text
#3852  singleton target configuration <-> direct gauge-group coordinate
#3854  split density and split mass = direct target density and mass
#3859  normalized split fiber pushes exactly to direct target coordinate
#3861  direct ground-state one-link weight
       = normalization * left vacuum * literal one-slab kernel * updated-right vacuum
```

This is the carrier bridge needed for a direct local Boltzmann-factor analysis.

---

# Phase 12 — Target-local one-slab action and kernel factorization

**Status: Integrated.**

The newest theorem stack is:

```text
#3863  right target update -> crossing variation + half right-spatial variation
#3866  crossing variation localizes exactly to the target-link Wilson energy change
#3869  intrinsic spatial Wilson action variation localizes to target-touching plaquettes
#3874  complete one-slab action variation is target-local
#3877  K(A, B[target <- g])
       = exp(-beta * DeltaS_targetLocal) * K(A,B)
#3880  define named localFactor and prove, for 0 <= beta,
       exp(-8 beta) <= localFactor <= exp(8 beta)
```

The #3880 constants are independent of configuration and lattice volume.

**What this does not yet prove:** normalized one-link minorization, contraction, Poincare/coercivity, spectral gap, or mass gap.

---

# Phase 13 — Normalize the target-local factor inside the ground-state fiber

**Status: Open now. Highest priority.**

The next proof unit should combine the direct ground-state one-link weight factorization from #3861 with the exact one-slab kernel multiplier and bounds from #3877/#3880.

A useful normalized target is one of the following equivalent-strength forms.

### Route A — normalized density-ratio bounds

Prove, with explicit volume-independent constants,

```text
c_-(beta) <= d nu_context1 / d nu_context2 <= c_+(beta)
```

for the relevant target-link probability fibers, under the exact same-root context relation used by the theorem.

### Route B — Doeblin minorization

Prove

```text
nu_context >= epsilon(beta) * nu_reference
```

for an explicit `epsilon(beta) > 0` independent of volume.

### Route C — conditional-variance comparison

If normalization algebra is cleaner in variance form, prove directly

```text
Var_target,ground(f) >= c(beta) * Var_target,reference(f)
```

with `c(beta) > 0` independent of volume.

### Required ingredients

```text
#3861 direct ground-state fiber weight factorization
#3877 exact target-local kernel multiplier
#3880 exp(+-8 beta) multiplier bounds
strict positivity of the relevant vacuum factors
exact target-fiber normalization identities
existing measurable Markov representative
```

### Non-negotiable boundary

The denominator must be controlled explicitly. An unnormalized pointwise factor bound cannot simply be renamed as a probability-measure minorization.

---

# Phase 14 — Convert normalized one-link control to the genuine joint projection defect

**Status: Open next.**

Once Phase 13 supplies a normalized one-link comparison, prove a lower bound for the actual ground-state joint target conditional variance, equivalently the genuine target projection defect

```text
||f - P_target f||^2.
```

The ideal output is a theorem whose constant depends on local coupling data such as `beta` but not on lattice volume.

Then use the already-integrated #3798 monotonicity

```text
||f - P_target f||^2
  <= ||f - P_color(target) f||^2
```

to inject the local estimate into the six-color residual.

---

# Phase 15 — Globalize without inverse-volume loss

**Status: Open next. Major obstruction.**

The main danger is a bound of the form

```text
color residual >= max_e oneLinkResidual(e)
```

followed by a naive average over all links of that color. This typically introduces a factor proportional to `1 / numberOfLinks`, which is useless for a scale-uniform gap.

A successful theorem must therefore use a genuinely uniform block mechanism, for example:

```text
block Poincare
approximate tensorization
a martingale variance decomposition
block conditional-expectation comparison
Dobrushin / Doeblin contraction
canonical paths / frame geometry
another same-root uniform mixing estimate
```

The best route should be selected from the actual formal structure available after Phase 13 rather than imposed abstractly in advance.

---

# Phase 16 — Scale-uniform twelve-spatial coercivity

**Status: Open. Central quantitative target.**

Prove

```text
there exists kappa > 0 such that
  for every scale n and every x in K_n,

  kappa ||x||^2 <= E12,n(R U x).
```

Requirements:

```text
kappa > 0
kappa independent of n
same-root physical carrier
no finite-dimensional compactness shortcut depending on n
no hidden weakening of the physical top-orthogonal sector
```

The implication machinery after this input is already largely formalized:

```text
uniform twelve-spatial Poincare kappa
  -> uniform six-spatial frame coefficient 2 kappa
  -> physical transfer gap >= 3 kappa / 4.
```

---

# Phase 17 — Uniform finite-volume physical transfer gap

**Status: Open downstream.**

Once a scale-independent `kappa` exists, package the resulting uniform physical transfer gap together with scale-uniform decay, resolvent, and Green estimates needed for a controlled limit.

Do not confuse the fixed-volume theorem network with the uniform family theorem.

---

# Phase 18 — Thermodynamic/scaling propagation

**Status: Open downstream.**

Required tasks include a same-root limit theorem that transports the uniform finite-volume physical information into the relevant continuum theory while preserving the vacuum/non-vacuum spectral separation.

This phase must control the relation between the finite Wilson physical transfer carrier and the continuum OS/Wightman carrier actually used for the final claim.

---

# Phase 19 — Clay-level completion

**Status: Open.**

Even after a uniform finite-volume transfer gap, the final Clay-level program still requires:

```text
full same-root four-dimensional continuum gauge field/state
required Euclidean/Wightman axiomatic control
physical OS reconstruction on that full carrier
correct vacuum structure
strictly positive continuum spectrum above vacuum
precise identification of the continuum mass gap
```

The repository should continue to state these obligations explicitly rather than folding them into the finite-lattice gap theorem.

---

# Immediate execution order from PR #3880

The recommended mathematical order is:

```text
1. Normalize the #3880 localFactor inside the direct ground-state target fiber.

2. Prove explicit probability-density ratio bounds or a Doeblin minorization
   with constants independent of volume.

3. Convert that normalized one-link theorem to a lower bound on the genuine
   ground-state joint target conditional variance / projection defect.

4. Feed the one-link bound into the containing six-color residual using the
   already-canonical #3798 nested-sigma monotonicity.

5. Prove a block/global theorem that avoids inverse-volume loss.

6. Deduce the scale-uniform twelve-spatial Poincare coefficient kappa.

7. Route kappa through the existing frame machinery to the physical transfer gap.

8. Only then attack the thermodynamic/scaling and full continuum physical bridge.
```

The current highest-priority theorem is therefore **normalized local-factor control on the actual ground-state one-link fiber**, not another qualitative kernel theorem and not a downstream continuum claim.

---

# Checkpoint

This roadmap is synchronized to the authoritative theorem checkpoint

```text
formal/real-hilbert-uniform-coercive-strong-limit
@ f65c0fc75c56ffdcba103331768b8aa73fbfba65
```

with exact validated head

```text
6f33df5b7d7f1c4258101b55a7d1372edfb15680
```

and

```text
PR Lean Fast Check #13579 = completed / success.
```
