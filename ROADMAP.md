# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-12 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

at the exact canonical theorem SHA

```text
015d3cceb59e696f692b6d67e017b3aee4664715
```

which is the normal merge commit of PR #3887:

```text
Transport sharp one-link Harnack to continuous physical vacuum
```

Validated exact theorem head:

```text
6b281139612a2c1188f2b6a616b2e1d986fb51c6
```

Validation:

```text
PR Lean Fast Check #13589 = completed / success
post-merge PR Lean Fast Check #13590 = completed / success
```

The public `main` branch is a landing/documentation surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status.

> **Current frontier**
>
> The explicit one-link fiber/disintegration layer is no longer the primary obstruction, and neither is the first target-local Wilson factorization. The canonical chain now contains the direct ground-state one-link weight, target-local Boltzmann factorization, uniform factor bounds, a pairwise target-local-factor comparison, the sharp raw-kernel one-link Harnack bound with factor `exp(8 beta)`, and the same `exp(8 beta)` Harnack bound for the canonical continuous physical vacuum representative.
>
> The highest-priority next theorem is to compose the raw-kernel and continuous-vacuum Harnack controls **on the exact direct ground-state one-link fiber carrier**, obtaining an explicit pairwise comparison for the complete unnormalized one-link weight. That result must then be normalized with explicit denominator control before any Doeblin/minorization or conditional-variance conclusion is claimed. The subsequent bottleneck is globalization to six-color / twelve-spatial coercivity without inverse-volume loss.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative theorem carrier.
- **Integrated implication machinery** — downstream implication is formalized, but a model-facing quantitative input remains.
- **Open now** — immediate constructive frontier.
- **Open next** — directly follows the current seam.
- **Open downstream** — required after the present quantitative frontier.
- **Parallel route** — useful independent route, not the immediate main line.
- **Diagnostic only** — correct information that must not be mistaken for the missing theorem.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model                         [Integrated]
  -> reflection positivity / boundary geometry                       [Integrated]
  -> literal one-slab Wilson kernel                                  [Integrated]
  -> physical spatial-slice transfer                                 [Integrated]
  -> positive / strictly-positive ground-state structure             [Integrated]

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

D. GROUND-STATE TWELVE-SPATIAL GEOMETRY

one-slab ground-state joint probability law                          [Integrated]
  -> 6 right + 6 left genuine spatial condExp projections            [Integrated]
  -> common fixed by all 12 = a.e. constants                         [Integrated]
  -> kernel(E12) = intrinsic constant line                           [Integrated]
  -> E12(R U x)=0 <-> x=0 on physical K                             [Integrated]

E. SAME-COLOR / GENUINE ONE-LINK GEOMETRY

same-color plaquette separation                                      [Integrated]
  -> raw Wilson target locality                                      [Integrated]
  -> same-color raw heat-bath commutation                            [Integrated]
  -> permutation-independent fixed-color Feller block                [Integrated]
  -> genuine joint target condExp                                    [Integrated]
  -> target residual <= containing color residual                    [Integrated]

F. EXPLICIT GROUND-STATE ONE-LINK FIBER / MARKOV LAYER

literal target fiber measure                                         [Integrated]
  -> target/off-target Haar split                                    [Integrated]
  -> a.e. measurable finite-positive fibers                          [Integrated]
  -> normalized target probability fibers                            [Integrated]
  -> measurable normalized Markov-kernel representative              [Integrated]
  -> exact global lintegral identity                                 [Integrated]
  -> original complete-right coordinate transport                    [Integrated]
  -> direct SU(N) target-coordinate bridge                           [Integrated]
  -> direct ground-state one-link Wilson/vacuum weight               [Integrated]

G. TARGET-LOCAL ONE-SLAB FACTORIZATION

right target update of one-slab action                               [Integrated]
  -> crossing target-link localization                               [Integrated]
  -> spatial target-link localization                                [Integrated]
  -> complete target-local action variation                          [Integrated]
  -> exact division-free kernel multiplier                           [Integrated]
  -> named localFactor                                                [Integrated]
  -> exp(-8 beta) <= localFactor <= exp(8 beta)                      [Integrated]

H. PAIRWISE HARNACK LAYER

direct ground-state weight -> localFactor bridge                     [Integrated: #3883]
localFactor(g) <= exp(16 beta) * localFactor(h)                       [Integrated: #3884]
raw kernel K(A,B[g]) <= exp(8 beta) * K(A,B[h])                      [Integrated: #3885]
RKHS synthesis = raw-kernel integral                                 [Integrated: #3887]
continuous-vacuum pointwise integral eigen-equation                  [Integrated: #3887]
Omega_c(B[g]) <= exp(8 beta) * Omega_c(B[h])                         [Integrated: #3887]

I. DIRECT GROUND-STATE ONE-LINK WEIGHT HARNACK

kernel Harnack + continuous-vacuum Harnack
  -> verify exact representative/carrier bridge used by direct fiber [OPEN NOW]
  -> complete one-link weight pairwise comparison                    [OPEN NOW]

J. NORMALIZED TARGET-FIBER COMPARISON

unnormalized one-link weight comparison
  -> normalization denominator control                               [OPEN NEXT]
  -> normalized density-ratio / Harnack bounds                       [OPEN NEXT]
  -> volume-independent minorization / Doeblin-type estimate         [OPEN NEXT]

K. GENUINE JOINT ONE-LINK QUANTITATIVE CONTROL

normalized target-fiber comparison
  -> lower bound on genuine target conditional variance              [OPEN NEXT]
  -> lower bound on target projection defect                         [OPEN NEXT]
  -> containing six-color residual receives the local information    [OPEN NEXT]

L. BLOCK / GLOBAL QUANTITATIVE SEAM

one-link information
  -> color/twelve-spatial estimate without 1/(number of links) loss [OPEN NEXT]

M. SCALE-UNIFORM TARGET

there exists kappa > 0, independent of n,
  for every scale n and every x in K_n,

  kappa ||x||^2 <= E12,n(R U x)                                      [OPEN]

  -> six-spatial frame coefficient 2 kappa                           [Integrated implication machinery]
  -> physical transfer gap >= 3 kappa / 4                            [Integrated implication machinery]

N. THERMODYNAMIC / CONTINUUM PHYSICAL PROPAGATION

uniform physical transfer gap                                       [Open downstream]
  -> stable Green / resolvent / decay bounds                         [Open downstream]
  -> controlled thermodynamic/scaling limit                          [Open downstream]
  -> physical OS/Wightman/Hamiltonian spectral lower bound           [Open downstream]

O. CLAY-LEVEL COMPLETION

full same-root 4D continuum gauge field/state                        [Open]
correct vacuum structure                                             [Open]
full physical OS/Wightman identification                             [Open]
strictly positive continuum spectrum above vacuum                    [Open]
Clay-level existence + mass gap                                      [Open]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository-operation rules for theorem work:

```text
start from the exact authoritative canonical SHA
use the theorem carrier, not public main, for theorem status
accept CI only at terminal completed / success
never treat queued / in_progress as success
write-freeze while exact-head CI is running
inspect the first genuine Lean error before editing a failed head
keep theorem development additive / tighten-only
never weaken physical assumptions silently
never identify unrelated carriers silently
forbid sorry / admit / new axiom / placeholder theorem declarations
fresh-check exact head / base / branch pointer before merge
normal-merge with expected head SHA fixed
verify merge parents and theorem-branch pointer after merge
verify post-merge CI
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
q_n < 1 for all n != inf_n (1-q_n) > 0
mutual absolute continuity != uniform L2 norm equivalence
raw Wilson locality != vacuum-weighted Doob locality without transport
measurable normalized fiber != RCD unless proved
unnormalized Harnack != normalized minorization without denominator control
one-link Harnack != global Poincare without a globalization theorem
pairwise commutation != Poincare lower bound
selected vacuum vector != full top eigenspace
one exact mode != global spectral floor
same-root scalar continuum != full 4D Yang--Mills field
green open PR != merged canonical theorem
public main != theorem authority
```

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The root is the actual periodic-even compact special-unitary Wilson Gibbs model. Integrated components include oriented lattice/edge/plaquette geometry, normalized Haar probability, Wilson action/Gibbs measure, reflection positivity, boundary and spatial-slice carriers, gauge-covariant holonomy, gauge-invariant observables, one-slab Wilson kernels, and physical transfer operators.

**Permanent rule:** keep the interacting Wilson model visible through every decisive physical bridge. Do not replace it by product Haar or an abstract projection system unless an explicit theorem supplies that transport.

---

# Phase 2 — Same-root continuum scalar OS construction

**Status: Integrated.**

The canonical lane contains finite gauge-invariant scalar readout, rational-time path laws, tight finite pushforward families, subsequential continuum probability laws, continuum reflection positivity, OS quotient/completion, a real strongly continuous contraction semigroup, a graph-closed self-adjoint Hamiltonian, normalized vacuum, and complete vacuum-orthogonal sector.

This is a same-root continuum scalar observable process, not yet the complete continuum gauge field on `R^4`.

---

# Phase 3 — Finite physical transfer and pair geometry

**Status: Integrated.**

At fixed volume the canonical branch contains the full top eigenspace, its orthogonal complement, the completed physical pair decomposition, strict non-top contraction, power decay, strong convergence, coercivity/spectral exclusion, resolvent bounds, Green operators, exact reduced ranges, and relative finite-volume Poincare estimates.

**Non-consequence:** fixed-volume strict contraction does not provide a scale-uniform gap.

---

# Phase 4 — Genuine twelve-spatial geometry and qualitative kernel closure

**Status: Integrated.**

The actual ground-state joint `L2` carrier supports six right and six left spatial conditional expectations. The canonical qualitative milestones include

```text
#3746  twelve-color common-fixed sector = ground-state-a.e. constants
#3768  E12(z)=0 iff represented function is ground-state-a.e. constant
#3770  a.e. constant iff equality with an actual constant vector
#3773  kernel(E12) = intrinsic real constant line
#3775  E12(R U x)=0 iff x=0 on the genuine physical full-top-orthogonal sector
```

The qualitative kernel problem is closed.

The downstream implication

```text
12-spatial Poincare kappa
  -> six-spatial frame coefficient 2 kappa
  -> physical transfer gap >= 3 kappa / 4
```

is already formalized.

**Permanent warning:** injectivity is not a positive scale-uniform coercivity constant.

---

# Phase 5 — Same-color Wilson locality and genuine one-link condExp

**Status: Integrated.**

The model-derived same-color chain includes

```text
#3779  distinct same-colored physical links cannot share a Wilson plaquette
#3781  separation descends to the actual six spatial color classes
#3783  compact Wilson target-local action separation
#3787  exact raw target one-link conditional-law locality
#3789  exact same-color raw heat-bath commutation
#3791  permutation-independent fixed-color Feller block
#3795  remote-replacement Doob normal form
#3798  genuine joint target condExp and target/color residual comparison
```

For the genuine target projection `P_target` and containing color projection `P_color`, the canonical geometry gives

```text
||f - P_target f|| <= ||f - P_color f||.
```

Thus a quantitative target-link lower bound can feed the containing color residual directly. The hard step remains obtaining such a bound and globalizing it uniformly.

---

# Phase 6 — Explicit ground-state one-link fiber and measurable Markov layer

**Status: Integrated.**

The former abstract disintegration frontier is now concrete:

```text
#3807  literal ground-state target fiber measure
#3810  normalize fixed fibers under explicit receipts
#3812  split target/off-target Haar coordinates measure-preservingly
#3815  a.e. target-fiber measurability
#3820  a.e. finite positive target-fiber mass
#3823  normalized a.e. target probability fibers
#3825  exact one-link fiber normalization identity
#3832  measurable normalized Markov-kernel representative
       + exact global lintegral identity
#3840  joint AE measurability in split coordinates
#3842  product-a.e. finite-positive fiber-mass control
#3845  ground-state split specialization
#3848  split-context Haar coordinate equivalence
#3850  original complete-right coordinate identity
#3852  singleton target <-> direct SU(N) measurable coordinate
#3854  split density/mass -> direct gauge coordinate
#3859  normalized split fiber -> direct target coordinate
#3861  direct one-link Wilson/vacuum weight factorization
```

**Claim boundary:** this measurable normalized kernel is not silently promoted to an RCD unless an exact identification theorem is supplied.

---

# Phase 7 — Target-local one-slab action and kernel factorization

**Status: Integrated.**

The exact local chain is

```text
#3863  right target update -> crossing variation + half right-spatial variation
#3866  crossing variation localizes exactly to target-link energy change
#3869  intrinsic spatial action variation localizes to target-touching plaquettes
#3874  complete one-slab action variation is target-local
#3877  K(A, B[target <- g])
       = exp(-beta * DeltaS_targetLocal) * K(A,B)
#3880  name localFactor and prove
       exp(-8 beta) <= localFactor <= exp(8 beta)
```

All constants here are configuration- and volume-independent.

---

# Phase 8 — Pairwise Harnack layer

**Status: Integrated through PR #3887.**

This is the principal advance beyond the previous public roadmap.

## 8.1 Direct ground-state weight / local-factor bridge — PR #3883

The direct one-link fiber weight is connected exactly to the target-local factorization. Schematically the weight has the visible structure

```text
transfer normalization
  * left vacuum
  * localFactor
  * base one-slab kernel
  * updated-right vacuum.
```

This exposes precisely which factors still vary with the target coordinate.

## 8.2 Pairwise local-factor Harnack — PR #3884

From the pointwise bounds of #3880, the canonical theorem gives

```text
localFactor(g) <= exp(16 beta) * localFactor(h)
```

for arbitrary `g,h`, with the symmetric reverse comparison.

This is useful but is not the sharpest kernel statement.

## 8.3 Sharp raw one-slab kernel Harnack — PR #3885

Rebasing the exact factorization at the comparison target value yields

```text
K(A, B[target <- g])
  <= exp(8 beta) * K(A, B[target <- h]),
```

again symmetrically, with a constant independent of the lattice volume.

The proof is division-free and uses the exact target-local kernel factorization, the local-factor upper bound, and kernel positivity.

## 8.4 Continuous physical vacuum Harnack — PR #3887

The canonical continuous physical vacuum representative now satisfies

```text
Omega_c(B[target <- g])
  <= exp(8 beta) * Omega_c(B[target <- h])
```

for arbitrary `g,h`, together with the reverse comparison.

The proof first closes two pointwise bridges:

```text
RKHS synthesis of Analysis(f)
  = integral_A f(A) K(A,B) dmu(A)

||T_phys|| * Omega_c(B)
  = integral_A Omega(A) K(A,B) dmu(A).
```

The raw-kernel Harnack is then integrated against the a.e. nonnegative top eigenvector and the strictly positive transfer norm is cancelled.

**Crucial carrier rule:** this avoids identifying an `L2` equivalence class with a pointwise eigenfunction. The pointwise theorem is about the already-canonical continuous representative.

---

# Phase 9 — Direct ground-state one-link weight Harnack

**Status: Open now.**

This is the immediate theorem frontier.

The direct ground-state one-link fiber already has a complete Wilson/vacuum factorization, while both varying ingredients now have pointwise pairwise Harnack bounds:

```text
raw one-slab kernel:      factor exp(8 beta)
continuous right vacuum: factor exp(8 beta)
```

A natural direct product route therefore suggests a complete-weight factor of order

```text
exp(16 beta),
```

but this is **not yet canonical**. Before asserting that constant, the proof must verify that the vacuum representative occurring in the exact direct-fiber factorization is definitionally the same as, or is connected by an explicit pointwise bridge to, the canonical continuous vacuum representative of #3887.

Target theorem shape:

```text
w_context(g) <= C(beta) * w_context(h)
```

with

```text
C(beta)
```

explicit and independent of lattice volume and context.

Requirements:

1. stay on the exact direct `SU(N)` target coordinate;
2. use the literal ground-state one-link weight already canonicalized;
3. make every vacuum-representative bridge explicit;
4. use no division when a positivity-preserving multiplicative proof suffices;
5. introduce no new assumptions and no RCD identification.

---

# Phase 10 — Normalize the target fiber

**Status: Open next.**

An unnormalized pairwise comparison is not yet a conditional-law theorem. The normalization denominator must be controlled explicitly.

Required chain:

```text
w(g) <= C w(h)
  -> comparison of fiber masses / normalizers
  -> normalized density-ratio bounds
  -> pairwise normalized Harnack comparison
  -> or a uniform minorization / Doeblin-type estimate.
```

The exact constant after normalization must be derived rather than guessed. Depending on the direction and normalization argument, constants can square or otherwise change; the roadmap therefore intentionally does not hard-code a normalized constant before the Lean theorem exists.

**Permanent warning:**

```text
unnormalized Harnack != normalized minorization.
```

---

# Phase 11 — Genuine joint one-link quantitative control

**Status: Open next.**

Once the normalized target-fiber law has an explicit volume-independent comparison/minorization theorem, convert it into a lower bound on genuine one-link conditional variance or, equivalently, a lower bound on the target projection defect.

Desired form:

```text
Var_target(f | off-target context)
  >= c(beta) * local_reference_variance(f)
```

or an equivalent spectral-gap / resampling inequality with `c(beta) > 0` independent of lattice volume.

Because #3798 already proves that the target residual is dominated by the containing color residual in the required direction, this result can feed the genuine six-color energy without rebuilding the sigma-algebra geometry.

---

# Phase 12 — Block/global quantitative seam

**Status: Open next; principal structural bottleneck after the one-link theorem.**

The central problem is to globalize one-link information without losing a factor proportional to the number of links.

Naive averaging of linkwise inequalities can produce

```text
kappa_n ~ 1 / (# links at scale n),
```

which is useless for the continuum mass-gap objective.

Acceptable routes may use the already-formalized six-color geometry, commuting/fixed-color blocks, conditional-expectation identities, or another exact finite-color mechanism, but the final theorem must produce a coefficient independent of scale.

**Forbidden shortcut:** qualitative kernel triviality cannot supply this coefficient by itself.

---

# Phase 13 — Scale-uniform twelve-spatial coercivity

**Status: Open.**

The decisive finite-volume target is

```text
exists kappa > 0,
  forall scale n,
  forall physical x in K_n,
    kappa * ||x||^2 <= E12,n(R U x).
```

with one `kappa` independent of `n`.

The downstream operator implication machinery is already integrated:

```text
scale-uniform twelve-spatial Poincare kappa
  -> six-spatial frame coefficient 2 kappa
  -> physical transfer gap >= 3 kappa / 4.
```

This is the point at which the local finite Wilson geometry becomes a genuine scale-uniform spectral statement.

---

# Phase 14 — Thermodynamic/scaling propagation

**Status: Open downstream.**

Even a scale-uniform finite-volume transfer gap is not automatically the complete continuum Yang--Mills mass-gap theorem. Further work must preserve the quantitative lower bound through the relevant thermodynamic/scaling construction and connect the resulting physical continuum carrier to the required field-theoretic formulation.

Required downstream objects include stable resolvent/Green/decay control, controlled limiting state/field construction, and a continuum Hamiltonian spectral lower bound above the vacuum.

---

# Phase 15 — Clay-level completion

**Status: Open.**

The final target requires, on one justified same-root chain:

```text
full four-dimensional continuum gauge field/state
  + Osterwalder-Schrader / Wightman structure
  + correct physical vacuum sector
  + self-adjoint Hamiltonian
  + strictly positive spectrum above the vacuum
  + the existence/regularity requirements of the Clay formulation.
```

The existing same-root scalar continuum OS lane is important infrastructure, but it is not identified with this full target.

---

# Recent canonical milestones

| PR | Result | Status |
|---|---|---|
| #3861 | direct ground-state one-link Wilson/vacuum factorization | Integrated |
| #3863 | one-slab right-target action variation bridge | Integrated |
| #3866 | right target-link crossing-action localization | Integrated |
| #3869 | spatial target-link Wilson action localization | Integrated |
| #3874 | complete target-local one-slab action variation | Integrated |
| #3877 | exact right-target kernel multiplier | Integrated |
| #3880 | localFactor with `exp(+-8 beta)` pointwise bounds | Integrated |
| #3883 | ground-state direct one-link weight -> target-local factor bridge | Integrated |
| #3884 | pairwise localFactor Harnack with `exp(16 beta)` | Integrated |
| #3885 | sharp raw one-slab kernel Harnack with `exp(8 beta)` | Integrated |
| #3887 | continuous physical vacuum Harnack with `exp(8 beta)` | Integrated |

---

# What should be proved next

The next mathematically coherent unit is:

```text
Direct ground-state one-link weight pairwise Harnack
```

not another abstract measure wrapper and not another fixed-volume spectral corollary.

A successful next PR should:

1. start exactly from canonical `015d3cceb59e696f692b6d67e017b3aee4664715`;
2. reuse the direct one-link weight factorization from #3861/#3883;
3. reuse the raw-kernel Harnack from #3885;
4. reuse the continuous-vacuum Harnack from #3887;
5. prove or expose the exact pointwise representative bridge needed by the direct fiber;
6. state an explicit pairwise weight comparison with a volume-independent constant;
7. make **no** normalized-law, coercivity, spectral-gap, or mass-gap claim unless separately proved.

After that theorem is canonical, normalization is the next coherent unit.

---

# Success criterion for the present quantitative program

The current finite-volume quantitative program is complete only when the repository contains a model-derived constant

```text
kappa > 0
```

that is independent of lattice scale and satisfies

```text
kappa ||x||^2 <= E12,n(R U x)
```

on every physical top-orthogonal sector `K_n`, with all carrier bridges explicit.

Until then, the correct public statement is:

> the qualitative physical kernel problem is closed; explicit one-link fibers and sharp volume-independent kernel/vacuum Harnack estimates are formalized; normalized one-link quantitative control and its volume-loss-free globalization remain open.
