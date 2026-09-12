# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-12 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest mathematical checkpoint before this documentation-only refresh is

```text
f74b992b8548734af7225c64314ad8fa18e21c0f
```

which is the normal merge of PR #3909,

```text
Identify continuous-vacuum and joint one-link fibers a.e.
```

Its exact proof head

```text
12445afbe35e0ed9645234355a4074ffce440243
```

passed `PR Lean Fast Check #13627` with terminal `completed / success`, including `Run changed Lean fast check = success`.

The public `main` branch is a landing surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status.

> **Current frontier**
>
> The repository now has a sharp volume-independent continuous-vacuum one-link Harnack theorem, sharp normalization / Doeblin comparison with only one `exp(16 beta)` factor, a corresponding sharp `exp(-16 beta)` one-link variance lower bound, and an almost-everywhere bridge from that direct normalized one-link law to the actual ground-state joint split target fiber.
>
> The immediate constructive task is therefore to consume the #3909 a.e. compatibility theorem inside the genuine ground-state conditional-expectation hierarchy, transfer the sharp one-link variance estimate to the actual joint one-link update, and then aggregate it to spatial block / color coercivity. Only after that step should the proof attempt the scale-independent twelve-block Poincaré theorem that feeds the already-integrated physical transfer-gap route.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated routing** — implication chain is formalized, but a model-derived quantitative input is still missing.
- **Open now** — immediate constructive frontier.
- **Open downstream** — required after the current frontier.
- **Parallel** — independent proof lane that should not be substituted for the global gap route.
- **Diagnostic only** — correct theorem/obstruction that informs strategy but is not the final mechanism.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model                         [Integrated]
  -> reflection positivity / boundary geometry                       [Integrated]
  -> physical one-slab transfer                                      [Integrated]
  -> positive / strictly-positive ground-state transfer geometry     [Integrated]

B. SAME-ROOT SCALAR CONTINUUM OS

finite Wilson scalar readout                                         [Integrated]
  -> rational / continuum scalar law                                 [Integrated]
  -> continuum OS positivity                                         [Integrated]
  -> direct-limit Hilbert carrier                                    [Integrated]
  -> real C0 semigroup                                                [Integrated]
  -> graph-closed self-adjoint Hamiltonian                           [Integrated]
  -> vacuum Omega / complete Omega-perp                              [Integrated]

C. FINITE PHYSICAL / GROUND-STATE JOINT-LAW ROUTE

physical top/non-top decomposition                                   [Integrated]
  -> finite-volume contraction / coercivity / resolvent / Green      [Integrated]
  -> one-slab ground-state joint probability law                     [Integrated]
  -> left/right boundary L2 isometries                               [Integrated]
  -> 6 right spatial condExp projections                             [Integrated]
  -> 6 left spatial condExp projections                              [Integrated]
  -> genuine 12-spatial family                                      [Integrated]
  -> E12 -> E6 -> raw physical defect -> transfer gap                [Integrated routing]

D. SHARP CONTINUOUS-VACUUM ONE-LINK CONTROL

complete one-link weight Wc                                          [Integrated: #3894]
  -> strict positivity / pairwise Harnack exp(16 beta)               [Integrated]
  -> normalized density rho                                         [Integrated: #3898]
  -> exp(-16 beta) <= rho <= exp(16 beta)                            [Integrated]
  -> exp(-16 beta) Haar <= nu <= exp(16 beta) Haar                   [Integrated]
  -> exp(-16 beta) one-link variance lower bound                     [Integrated: #3907]

E. ACTUAL JOINT-FIBER COMPATIBILITY

continuous-vacuum direct one-link law
  -> target/off-target Haar split                                    [Integrated]
  -> a.e. equality with legacy ground-state split target fiber       [Integrated: #3909]
  -> exact target-evaluation Measure.map back to SU(N)               [Integrated]

F. IMMEDIATE LOCAL-TO-GENUINE UPDATE BRIDGE

sharp direct one-link variance
  + #3909 a.e. fiber compatibility
  -> actual joint one-link conditional variance / residual            [OPEN NOW]

G. BLOCK / COLOR AGGREGATION

actual one-link residuals
  -> one spatial color block                                         [OPEN NOW]
  -> six right blocks + six left blocks                              [OPEN NOW]
  -> quantitative E12 control                                        [OPEN NOW]

H. GLOBAL COERCIVITY

identify relevant 12-block common-fixed sector                       [OPEN NOW]
  -> Poincare on its orthogonal complement                           [OPEN NOW]
  -> positive scale-independent kappa_*                              [OPEN NOW]
  -> physical transfer gap >= 3 kappa_*/4                            [Integrated routing]

I. THERMODYNAMIC / CONTINUUM PROPAGATION

uniform finite-volume physical transfer gap                          [OPEN DOWNSTREAM]
  -> stable Green/resolvent/Poincare control                         [OPEN DOWNSTREAM]
  -> thermodynamic/scaling-limit physical carrier                    [OPEN DOWNSTREAM]
  -> physical OS/Wightman spectral lower bound                       [OPEN DOWNSTREAM]

J. CLAY-LEVEL COMPLETION

sufficiently rich same-root 4D continuum Yang--Mills field/state     [OPEN]
correct vacuum structure / nontriviality                             [OPEN]
physical OS/Wightman identification                                  [OPEN]
strict positive spectrum above the vacuum sector                     [OPEN]
Clay-level existence + mass gap                                      [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository-operation rules for theorem work:

```text
start from the exact authoritative canonical SHA
use GitHub-mediated repository operations
accept CI only when workflow / job / Lean step are terminal success
never treat queued or in_progress as success
write-freeze while exact-head CI is running
inspect the first genuine terminal Lean failure before editing
keep theorem development additive / tighten-only
forbid proof placeholders in theorem source
merge with expected head SHA fixed
verify merge parents and canonical branch pointer
```

Claim discipline:

```text
finite theorem != continuum theorem
positive coefficient at each scale != uniform positive coefficient
local Harnack / Doeblin / variance != global L2 Poincare
qualitative fixed-space statement != quantitative coercivity
relative top-sector control != unique-vacuum control
one selected positive mode != global spectral floor
same-root scalar continuum != full 4D Yang--Mills field
green open PR != merged canonical theorem status
```

At the #3909 proof checkpoint, CI used Lean `4.30.0-rc2` and Lake `5.0.0-src+3dc1a08`.

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The finite root is the interacting periodic-even compact special-unitary Wilson Gibbs model.

Integrated components include:

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
one-slab Wilson kernels and transfer operators
```

Permanent rule: keep the interacting Wilson model visible through every decisive physical bridge. Product Haar may be used as a reference measure only through explicit comparison theorems.

---

# Phase 2 — Same-root scalar continuum OS construction

**Status: Integrated.**

Integrated route:

```text
finite primary gauge-invariant scalar readout
  -> reflection-completed rational-time path
  -> tight finite pushforward laws
  -> Prokhorov subsequential continuum probability law
  -> continuum reflection positivity
  -> OS quotient / Hilbert completion
  -> real strongly continuous contraction semigroup
  -> graph-closed self-adjoint Hamiltonian
  -> normalized vacuum Omega
  -> complete vacuum-orthogonal sector Omega-perp
```

This is a genuine same-root continuum observable process, not yet the complete four-dimensional gauge field.

---

# Phase 3 — Finite physical-pair and spectral machinery

**Status: Integrated.**

The fixed-finite-volume program contains the physical top/non-top decomposition and the corresponding analytic consequences:

```text
strict non-top contraction
power decay / strong convergence
fixed-space characterization
coercivity
real spectral confinement
resolvent estimates
Green operator
exact reduced range
relative Poincare estimates
```

This machinery is now downstream infrastructure. The active proof program seeks a model-derived quantitative source of separation in the actual ground-state conditional-expectation dynamics.

---

# Phase 4 — Ground-state joint law and genuine twelve-spatial dynamics

**Status: Integrated.**

The canonical branch contains:

```text
strictly positive physical ground-state structure
ground-state normalized one-slab law
genuine left/right joint probability measure
left/right boundary L2 isometries
coarse conditional expectation / Doob boundary geometry
6 genuine right spatial conditional expectations
6 genuine left spatial conditional expectations
explicit two-sided 12-spatial family
qualitative common-fixed characterization
```

The twelve-spatial physical routing introduced earlier is now canonical. In particular, on right-boundary lifts the conventional twelve-block residual reduces to one half of the six-right residual, and the integrated implication chain gives

```text
12-block Poincare coefficient kappa
  -> six-spatial frame coefficient 2 kappa
  -> physical transfer gap >= 3 kappa / 4.
```

This is an implication route. It does not supply `kappa` by itself.

---

# Phase 5 — Complete continuous-vacuum one-link Harnack

**Status: Integrated through PR #3894.**

Define the complete direct one-link weight using the canonical continuous physical-vacuum representative:

```text
Wc(g)
  = ||T||^{-1}
    * Omega_c(left)
    * K(left, right[target <- g])
    * Omega_c(right[target <- g]).
```

The canonical branch proves:

```text
0 < Wc(g)
Wc(g) <= exp(16 beta) Wc(h)
```

for all one-link values `g,h`.

The proof combines the raw-kernel and continuous-vacuum Harnack factors without evaluating an arbitrary `L²` representative pointwise.

Completion criterion: already satisfied.

---

# Phase 6 — Normalize the complete one-link law sharply

**Status: Integrated through PR #3898.**

Let

```text
mu  = normalized compact Haar on SU(N)
Z   = integral Wc dmu
rho = Wc / Z
nu  = rho * mu
R   = exp(16 beta).
```

By integrating the pairwise Harnack inequality directly, the canonical branch proves

```text
0 < Z < infinity
R^{-1} <= rho(g) <= R
R^{-1} mu <= nu <= R mu.
```

The direct pairwise route is important: it avoids the unnecessary `R^2 = exp(32 beta)` loss that would arise from separately anchoring global lower and upper weight bounds.

Completion criterion: already satisfied.

---

# Phase 7 — Transfer normalized Doeblin control to one-link variance

**Status: Integrated through PR #3907.**

The canonical branch consumes the normalized measure comparison directly at the centered-residual / best-constant / variance layer.

For appropriate `L²` observables,

```text
R^{-1} * evariance_mu(X) <= evariance_nu(X)
```

with

```text
R^{-1} = exp(-16 beta).
```

The proof also transports `MemLp` from Haar to `nu` using the upper measure bound.

This is the sharp local quantitative input currently available for the block-dynamics program.

Completion criterion: already satisfied.

---

# Phase 8 — Bridge the direct continuous-vacuum law to the actual joint split fiber

**Status: Integrated through PR #3909.**

The direct continuous-vacuum law and the legacy joint density use representatives that agree only almost everywhere. Therefore the correct theorem is an a.e. compatibility statement.

The integrated route:

```text
1. reconstructs a complete right boundary from retained off-target coordinates;
2. uses Omega_c = Omega almost everywhere under spatial-slice Haar;
3. transports that equality through the exact target/off-target Haar split;
4. proves equality of normalized split target fibers for
   Haar-a.e. left boundary and Haar-a.e. retained off-target context;
5. proves exact singleton-target Measure.map transport back to SU(N);
6. combines the two into an a.e. compatibility theorem for the actual
   ground-state split one-link fiber.
```

This theorem deliberately preserves exceptional outer contexts. It does not claim RCD identification and does not promote an arbitrary `L²` representative to a pointwise function.

Completion criterion: already satisfied.

---

# Phase 9 — Transfer sharp one-link variance to the genuine joint update

**Status: OPEN NOW — immediate frontier.**

The next theorem should consume Phase 8 rather than reprove local Harnack information.

Target architecture:

```text
sharp direct normalized one-link variance theorem
  + a.e. equality of actual split target fibers
  + exact target-coordinate measure equivalence
  -> variance / centered-residual lower bound for the actual joint
     one-link update used by the ground-state conditional-expectation lane.
```

The theorem should be stated on the actual joint probability carrier and should preserve the `exp(-16 beta)` factor whenever the measure-theoretic transport permits it.

### Critical constraints

```text
no pointwise evaluation of the legacy quotient representative
no replacement of a.e. fiber equality by universal equality
no implicit RCD identification
no new exp(-32 beta) loss unless mathematically forced
```

### Completion criterion

A canonical theorem applies the sharp one-link variance estimate directly to the genuine joint one-link conditional update for a.e. outer context, in the exact form needed by block/color aggregation.

---

# Phase 10 — Aggregate one-link variance to spatial color blocks

**Status: OPEN NOW.**

Once Phase 9 is available, aggregate the genuine one-link residuals belonging to one spatial color class.

The target is not merely a sum of unrelated inequalities. The proof should use the actual spatial matching / disjoint-update geometry already present in the repository so that the coefficient does not acquire artificial volume dependence.

Desired schematic result:

```text
sum of one-link conditional variances in color c
  -> lower bound for the color-c conditional-expectation residual
  -> coefficient controlled by model parameters rather than number of links.
```

### Completion criterion

A theorem on the ground-state joint carrier bounds the residual of each genuine spatial-color conditional expectation from below by explicit local variance data with controlled constants.

---

# Phase 11 — Assemble six-right and six-left block coercivity

**Status: OPEN NOW.**

Combine the six right spatial color blocks and the six left spatial color blocks on the same joint `L²` carrier.

The integrated twelve-spatial identity already supplies the normalization bookkeeping. What is still required is a genuine lower bound for the corresponding Dirichlet form.

Target:

```text
E12(z)
  = (1/12) sum over 12 spatial blocks ||z - P_c z||^2
  >= explicit model-derived coercive quantity.
```

This phase should stay on the actual ground-state joint law and avoid introducing an abstract replacement projection family.

---

# Phase 12 — Identify the relevant twelve-block common-fixed sector

**Status: OPEN NOW.**

The repository already proves qualitative simultaneous fixedness under the right-six and left-six halves. The next geometric theorem must identify the common-fixed sector strongly enough to place the relevant physical top-orthogonal right-boundary lifts in its orthogonal complement.

Do **not** assert that the common-fixed space is constants unless the retained sigma-algebras and joint measure actually prove that statement.

### Completion criterion

A theorem identifies the exact common-fixed sector needed by the block Poincaré theorem and connects it to the physical top/common sector without an independent assumption.

---

# Phase 13 — Prove a finite-volume twelve-block `L²` Poincaré theorem

**Status: OPEN NOW.**

After Phases 9--12, prove

```text
kappa(H,N,beta) * ||z||^2 <= E12(z)
```

on the orthogonal complement of the identified common-fixed sector, with `kappa(H,N,beta) > 0` derived from the actual model.

This theorem must be a genuine `L²` coercivity statement. Total-variation / Dobrushin influence control may support it but may not be silently substituted for it.

### Completion criterion

A model-derived finite-volume positive coefficient is proved on the actual ground-state twelve-block dynamics.

---

# Phase 14 — Make the coefficient scale-independent

**Status: OPEN NOW — decisive quantitative milestone.**

A positive coefficient at each finite scale is not sufficient. Along the physical scaling family we need a uniform lower bound

```text
exists kappa_* > 0, for every relevant scale n,
  kappa_* * ||z||^2 <= E12_n(z).
```

The coefficient must come from quantities whose dependence on volume, lattice spacing, and coupling is explicitly controlled.

Two acceptable outcomes:

```text
A. uniform coercivity succeeds
   -> retain explicit kappa_* > 0;

B. the candidate coefficient degenerates
   -> prove the degeneration honestly;
   -> identify the losing estimate;
   -> replace it with stronger block / multiscale / geometry-aware control.
```

Never hide scale degeneration behind a uniform hypothesis.

---

# Phase 15 — Invoke the integrated physical transfer-gap route

**Status: Integrated routing; waiting for Phase 14 input.**

Once a uniform twelve-block coefficient exists, no new abstract gap lemma is needed. The canonical route already gives

```text
uniform twelve-block Poincare kappa_*
  -> six-spatial frame coefficient 2 kappa_*
  -> raw physical squared-defect coercivity
  -> physical transfer gap >= 3 kappa_* / 4.
```

The main theorem work here should therefore be specialization and carrier bookkeeping, not a new replacement proof architecture.

---

# Phase 16 — Uniform finite-volume analytic consequences

**Status: OPEN DOWNSTREAM.**

Feed the uniform physical gap into the already-integrated finite-volume machinery to obtain stable versions of

```text
non-top contraction / decay
coercivity
resolvent control
Green bounds
relative Poincare estimates
reduced-range control
```

on the correct physical/common-fixed sector.

---

# Phase 17 — Thermodynamic and scaling-limit propagation

**Status: OPEN DOWNSTREAM.**

Propagate the uniform finite-volume information without losing same-root provenance.

Possible ingredients include:

```text
tightness / compactness for the physical state family
compatibility of finite-volume Hilbert carriers
form / Mosco / strong-resolvent convergence as appropriate
stability of the vacuum/common-fixed sector
passage of a positive lower spectral bound to the limiting operator
```

A uniform finite-volume inequality alone is not yet a continuum mass-gap theorem. The limiting physical carrier and operator must be constructed and identified.

---

# Phase 18 — Full same-root physical continuum carrier

**Status: OPEN DOWNSTREAM.**

The existing scalar continuum OS lane is substantial but not yet the complete four-dimensional Yang--Mills field/state required for Clay-level completion.

Required work includes a coherent version of

```text
continuum gauge-invariant local observable algebra / distributions
Euclidean covariance
reflection positivity
regularity sufficient for OS reconstruction
physical nontriviality
physical Hilbert carrier
Hamiltonian and vacuum
connection to the finite Wilson approximants
```

---

# Phase 19 — Physical OS/Wightman spectral gap

**Status: OPEN DOWNSTREAM.**

After the full same-root physical continuum carrier is established, transfer the uniform finite-volume coercivity into a statement of the form

```text
spectrum(H_phys | Omega-perp) subset [m, infinity)
```

for some `m > 0`, or the correct equivalent formulation if the vacuum sector is not one-dimensional.

This is where the finite-volume transfer-gap program becomes a continuum mass-gap theorem.

---

# Phase 20 — Clay-level completion

**Status: OPEN.**

A completed theorem must combine, on one coherent same-root construction,

```text
4D continuum Yang--Mills existence
Euclidean covariance
reflection positivity / OS axioms in the required form
regularity / distributional field structure
physical nontriviality
correct vacuum structure
physical OS/Wightman Hilbert realization
strictly positive spectral gap above the vacuum sector
```

Only after those obligations are discharged should the repository claim a complete Yang--Mills existence-and-mass-gap theorem.

---

# Parallel lane — SU(2) selected exact mode

**Status: Parallel; implication machinery is integrated, raw-model realization remains separate.**

The selected exact-mode route seeks an attained positive-energy mode from raw Wilson data. It is useful but logically different from the twelve-block Poincaré program.

Permanent distinction:

```text
one selected exact positive mode
  != lower spectral bound for the whole physical orthogonal sector.
```

Do not substitute exact-mode realization for the global coercivity theorem.

---

# Diagnostic lane — finite-volume Dobrushin / influence control

**Status: Diagnostic only for the continuum gap question.**

The repository contains explicit finite-volume Wilson/Dobrushin information. Such bounds remain useful for local conditional-law dependence and may enter a block argument.

However the simple coefficient based on

```text
(exp(4 beta)-1)/(exp(4 beta)+1)
```

approaches `1` as `beta -> +infinity`. That mechanism alone therefore cannot be presented as the final scale-independent continuum-gap proof in the relevant large-`beta` regime.

This obstruction motivates stronger ground-state / block / geometry-aware coercivity rather than invalidating the program.

---

# Immediate execution order

The recommended next sequence is:

```text
1. consume PR #3909 and transfer the sharp exp(-16 beta) variance bound
   to the genuine ground-state joint one-link update;
2. express that theorem directly in the conditional-expectation residual API;
3. aggregate one-link residuals to one spatial color block using the actual
   matching/disjoint-update geometry;
4. prove corresponding right-six and left-six block estimates;
5. combine them into quantitative twelve-block Dirichlet control;
6. identify the exact twelve-block common-fixed sector relevant to physical
   top-orthogonal right-boundary lifts;
7. prove a positive finite-volume twelve-block Poincare coefficient;
8. make the coefficient scale-independent or prove precisely where the
   candidate coefficient degenerates;
9. invoke the already-integrated E12 -> E6 -> raw defect -> transfer-gap route;
10. propagate the uniform physical gap through the same-root thermodynamic /
    continuum construction.
```

This order avoids redoing solved local analysis and keeps the next theorem attached to the actual ground-state joint probability law.

---

# Definition of success for the present milestone

The present local-to-block milestone is complete only when Lean contains a theorem chain of the form

```text
sharp continuous-vacuum one-link variance
  + a.e. actual joint-fiber compatibility
  -> genuine joint one-link residual inequality
  -> spatial color-block residual inequality
  -> quantitative twelve-block Dirichlet control.
```

The next major mass-gap milestone is complete only when that chain further yields

```text
actual ground-state twelve-block dynamics
  -> identified common-fixed sector
  -> exists kappa_* > 0 uniformly across the physical scaling family
  -> physical transfer gap >= 3 kappa_* / 4.
```

Until the uniform model-derived coefficient and its same-root continuum propagation are proved, the global Yang--Mills mass-gap boundary remains open.
