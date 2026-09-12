# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-13 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest mathematical baseline before this documentation refresh is

```text
282913e02c660d0181ee69e552bf374549adc8d4
```

which is the normal merge of PR #3926,

```text
Transfer sharp one-link variance to ground-state joint split fibers
```

with first parent

```text
4cce50198af53abd6449edafcd16f0fab4f4b2e3
```

which is the normal merge of PR #3921,

```text
Transfer sharp one-link variance to actual ground-state split fiber
```

Exact proof heads and validation:

```text
PR #3921
  head: 1c755f07b1add1480ab1ae8287d847da8462d1bb
  PR Lean Fast Check #13632
  workflow run 34699024449
  completed / success

PR #3926
  head: db95f664ed50084cd68fc42621793d97189c0d81
  PR Lean Fast Check #13637
  workflow run 34722528934
  completed / success
```

The public `main` branch is a landing surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status.

> **Current frontier**
>
> The repository now has the complete sharp local chain from continuous-vacuum one-link Harnack through normalization, Doeblin comparison, sharp `exp(-16 beta)` one-link variance, a.e. identification with the actual ground-state split fiber, and transfer of the variance / residual estimate to that actual split fiber for a.e. outer context.
>
> The immediate constructive task is **not** another one-link Harnack or another fiber-identification theorem. It is to connect the canonical #3921/#3926 fiberwise estimate to the genuine ground-state `condExpL2` residual on the actual joint `L²` carrier, integrate over outer contexts, and then aggregate to spatial color blocks.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated routing** — implication chain is formalized, but a model-derived quantitative input is still missing.
- **Open now** — immediate constructive frontier.
- **Open downstream** — required after the current frontier.
- **Parallel** — independent proof lane that must not be substituted for the global gap route.
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

complete one-link weight Wc                                          [#3894, Integrated]
  -> strict positivity / pairwise Harnack exp(16 beta)               [Integrated]
  -> normalized density rho                                         [#3898, Integrated]
  -> exp(-16 beta) <= rho <= exp(16 beta)                            [Integrated]
  -> exp(-16 beta) Haar <= nu <= exp(16 beta) Haar                   [Integrated]
  -> exp(-16 beta) one-link variance lower bound                     [#3907, Integrated]

E. ACTUAL JOINT-FIBER COMPATIBILITY

continuous-vacuum direct one-link law
  -> target/off-target Haar split                                    [Integrated]
  -> a.e. equality with legacy ground-state split target fiber       [#3909, Integrated]
  -> exact target-evaluation Measure.map back to SU(N)               [Integrated]

F. ACTUAL GROUND-STATE SPLIT-FIBER VARIANCE

sharp direct one-link residual / variance
  + a.e. actual split-fiber compatibility
  -> a.e. fixed-center residual lower bound                          [#3921, Integrated]
  -> a.e. best-constant residual lower bound                         [#3921, Integrated]
  -> a.e. evariance lower bound                                      [#3921, Integrated]
  -> IdentDistrib target-evaluation transport                        [#3926, Integrated]
  -> sharp exp(-16 beta) actual joint split-fiber variance           [#3926, Integrated]

G. GENUINE CONDITIONAL-EXPECTATION BRIDGE

a.e. actual split-fiber variance
  -> actual joint condExpL2 residual coercivity                       [OPEN NOW]
  -> outer-context integration / measurable residual identity         [OPEN NOW]

H. BLOCK / COLOR AGGREGATION

genuine one-link condExp residuals
  -> one spatial color block                                         [OPEN NOW]
  -> six right blocks + six left blocks                              [OPEN NOW]
  -> quantitative E12 control                                        [OPEN NOW]

I. GLOBAL FINITE-VOLUME COERCIVITY

identify relevant 12-block common-fixed sector                       [OPEN NOW]
  -> finite-volume Poincare on its orthogonal complement              [OPEN NOW]
  -> positive model-derived kappa(H,N,beta)                          [OPEN NOW]
  -> scale-independent kappa_*                                       [OPEN NOW]
  -> physical transfer gap >= 3 kappa_*/4                            [Integrated routing]

J. THERMODYNAMIC / CONTINUUM PROPAGATION

uniform finite-volume physical transfer gap                          [OPEN DOWNSTREAM]
  -> stable Green/resolvent/Poincare control                         [OPEN DOWNSTREAM]
  -> thermodynamic/scaling-limit physical carrier                    [OPEN DOWNSTREAM]
  -> physical OS/Wightman spectral lower bound                       [OPEN DOWNSTREAM]

K. CLAY-LEVEL COMPLETION

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
fiberwise a.e. variance != global condExpL2 residual coercivity
qualitative fixed-space statement != quantitative coercivity
relative top-sector control != unique-vacuum control
one selected positive mode != global spectral floor
same-root scalar continuum != full 4D Yang--Mills field
green open PR != merged canonical theorem status
```

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The finite root is the interacting periodic-even compact special-unitary Wilson Gibbs model.

Integrated components include:

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
one-slab Wilson kernels and transfer operators
```

Permanent rule: keep the interacting Wilson model visible through every decisive physical bridge. Product Haar is a reference measure only through explicit comparison theorems.

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

This is a genuine same-root continuum observable process, not yet the complete four-dimensional gauge field/state.

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

This machinery is downstream infrastructure. The active proof program seeks a model-derived quantitative source of separation from the actual ground-state conditional-expectation dynamics.

---

# Phase 4 — Ground-state joint law and genuine twelve-spatial dynamics

**Status: Integrated.**

The authoritative branch contains:

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

The twelve-spatial physical routing is canonical. On the relevant right-boundary lifts, the normalization bookkeeping yields the integrated implication chain

```text
12-block Poincare coefficient kappa
  -> six-spatial frame coefficient 2 kappa
  -> physical transfer gap >= 3 kappa / 4.
```

This is an implication route. It does not supply `kappa` by itself.

---

# Phase 5 — Complete continuous-vacuum one-link Harnack

**Status: Integrated through PR #3894.**

For the complete direct one-link weight `Wc`, the authoritative branch proves

```text
0 < Wc(g)
Wc(g) <= exp(16 beta) Wc(h)
```

for all one-link values `g,h`.

The proof combines the raw-kernel and continuous-vacuum factors without pointwise evaluation of an arbitrary `L²` quotient representative.

Completion criterion: satisfied.

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

The authoritative branch proves

```text
0 < Z < infinity
R^{-1} <= rho(g) <= R
R^{-1} mu <= nu <= R mu.
```

The pairwise Harnack inequality is integrated directly. No artificial `R^2 = exp(32 beta)` loss is introduced.

Completion criterion: satisfied.

---

# Phase 7 — Transfer normalized Doeblin control to one-link variance

**Status: Integrated through PR #3907.**

For appropriate Haar-`L²` observables,

```text
R^{-1} * evariance_mu(X) <= evariance_nu(X)
```

with

```text
R^{-1} = exp(-16 beta).
```

The proof also transports `MemLp` from Haar to the normalized one-link law using the upper measure comparison.

Completion criterion: satisfied.

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
6. combines these into a.e. compatibility with the actual split fiber.
```

This theorem preserves exceptional contexts. It does not claim an RCD identification and does not promote an arbitrary `L²` representative to a pointwise function.

Completion criterion: satisfied.

---

# Phase 9 — Transfer sharp variance to the actual ground-state split fiber

**Status: Integrated through PRs #3921 and #3926.**

This phase was the previous immediate frontier and is now complete.

PR #3921 adds the model-facing transfer layer through files including

```text
PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkContextVarianceTransfer.lean
PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkJointVarianceTransfer.lean
PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointObservableOneLinkVariance.lean
```

It transfers the sharp direct one-link control through the #3909 a.e. fiber compatibility theorem and establishes, for a.e. outer context, the actual split-fiber analogues of:

```text
fixed-center squared-residual lower bounds
best-constant squared-residual lower bounds
extended variance lower bounds.
```

PR #3926 adds the focused theorem file

```text
PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkVarianceTransfer.lean
```

and uses exact target-evaluation pushforward plus `ProbabilityTheory.IdentDistrib` to transport `evariance` without an extra constant loss.

The resulting quantitative statement preserves

```text
exp(-16 beta)
```

as the local lower-bound coefficient on the actual ground-state joint split fiber for a.e. outer context.

### Permanent constraints retained by the integrated theorem

```text
no pointwise evaluation of the legacy quotient representative
no promotion of a.e. fiber equality to universal equality
no implicit RCD identification
no extra exp(-32 beta) loss
```

Completion criterion: satisfied.

---

# Phase 10 — Connect split-fiber variance to the genuine `condExpL2` residual

**Status: OPEN NOW — immediate frontier.**

This is the next mathematically coherent unit.

The goal is to consume Phase 9 inside the actual ground-state joint conditional-expectation API:

```text
a.e. actual split-fiber variance lower bound
  + measurable outer-context dependence
  + actual joint disintegration / conditional-expectation identities
  -> global one-link condExpL2 residual lower bound.
```

The desired result should live on the actual joint `L²` carrier and should be stated in the same residual language used by the genuine spatial conditional expectations.

### Critical constraints

```text
fiberwise evariance is not yet condExpL2 coercivity
keep all a.e. quantifiers tied to their correct measures
do not combine unrelated Eventually statements casually
do not evaluate arbitrary L2 representatives pointwise
do not assert RCD identification unless explicitly proved
preserve exp(-16 beta) unless a genuine integration step forces loss
```

### Completion criterion

A canonical theorem bounds the squared residual of the genuine one-link `condExpL2` update from below by the corresponding Haar variance datum with a model-controlled coefficient, on the actual joint probability carrier.

---

# Phase 11 — Aggregate genuine one-link residuals to one spatial color block

**Status: OPEN NOW.**

Once Phase 10 is available, aggregate the actual one-link residuals belonging to one spatial color class.

The proof must use the existing spatial matching / disjoint-update geometry rather than merely summing unrelated local inequalities.

Desired schematic result:

```text
sum of genuine one-link conditional residuals in color c
  -> lower bound for the color-c conditional-expectation residual
  -> coefficient controlled by model parameters rather than link count.
```

### Completion criterion

A theorem on the actual ground-state joint carrier bounds each spatial-color conditional-expectation residual by explicit local variance data with volume dependence under control.

---

# Phase 12 — Assemble six-right and six-left block coercivity

**Status: OPEN NOW.**

Combine the six right spatial color blocks and the six left spatial color blocks on the same joint `L²` carrier.

Target:

```text
E12(z)
  = (1/12) sum over the 12 genuine spatial blocks ||z - P_c z||^2
  >= explicit model-derived coercive quantity.
```

The theorem must stay on the actual ground-state joint law and must not replace the genuine conditional expectations with an abstract projection family.

---

# Phase 13 — Identify the relevant twelve-block common-fixed sector

**Status: OPEN NOW.**

The repository already contains qualitative simultaneous-fixedness information for the right-six and left-six halves. The next geometric theorem must identify the common-fixed sector strongly enough to place the relevant physical top-orthogonal right-boundary lifts in its orthogonal complement.

Do **not** assert that the common-fixed space is constants unless the retained sigma-algebras and actual joint measure prove that statement.

### Completion criterion

A theorem identifies the exact common-fixed sector required by the block Poincare argument and connects it to the physical top/common sector without an independent assumption.

---

# Phase 14 — Prove a finite-volume twelve-block `L²` Poincare theorem

**Status: OPEN NOW.**

After Phases 10--13, prove

```text
kappa(H,N,beta) * ||z||^2 <= E12(z)
```

on the orthogonal complement of the identified common-fixed sector, with

```text
kappa(H,N,beta) > 0
```

derived from the actual model.

This must be a genuine `L²` coercivity theorem. Total-variation or Dobrushin influence control may support it but may not be silently substituted for it.

### Completion criterion

A model-derived positive finite-volume coefficient is proved on the genuine ground-state twelve-block dynamics.

---

# Phase 15 — Make the coefficient scale-independent

**Status: OPEN NOW — decisive quantitative milestone.**

A positive coefficient at each finite scale is not enough. Along the physical scaling family one needs

```text
exists kappa_* > 0, for every relevant scale n,
  kappa_* * ||z||^2 <= E12_n(z).
```

The coefficient must come from quantities whose dependence on volume, lattice spacing, and coupling is explicitly controlled.

Two acceptable outcomes:

```text
A. uniform coercivity succeeds
   -> retain explicit kappa_* > 0;

B. the proposed coefficient degenerates
   -> prove the degeneration honestly;
   -> identify the losing estimate;
   -> replace it with stronger block / multiscale / geometry-aware control.
```

Never hide scale degeneration behind a uniform hypothesis.

---

# Phase 16 — Invoke the integrated physical transfer-gap route

**Status: Integrated routing; waiting for Phase 15 input.**

Once a uniform twelve-block coefficient exists, no new abstract gap architecture is needed. The canonical route already gives

```text
uniform twelve-block Poincare kappa_*
  -> six-spatial frame coefficient 2 kappa_*
  -> raw physical squared-defect coercivity
  -> physical transfer gap >= 3 kappa_*/4.
```

The theorem work here should therefore be specialization and carrier bookkeeping, not a new replacement proof architecture.

---

# Phase 17 — Uniform finite-volume analytic consequences

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

# Phase 18 — Thermodynamic and scaling-limit propagation

**Status: OPEN DOWNSTREAM.**

Propagate the uniform finite-volume information without losing same-root provenance.

Possible ingredients include

```text
tightness / compactness for the physical state family
compatibility of finite-volume Hilbert carriers
form / Mosco / strong-resolvent convergence as appropriate
stability of the vacuum/common-fixed sector
passage of a positive lower spectral bound to the limiting operator.
```

A uniform finite-volume inequality alone is not yet a continuum mass-gap theorem. The limiting physical carrier and operator must be constructed and identified.

---

# Phase 19 — Full same-root physical continuum carrier

**Status: OPEN DOWNSTREAM.**

The existing scalar continuum OS lane is substantial but is not yet the complete four-dimensional Yang--Mills field/state required for Clay-level completion.

Required work includes a coherent version of

```text
continuum gauge-invariant local observable algebra / distributions
Euclidean covariance
reflection positivity
regularity sufficient for OS reconstruction
physical nontriviality
physical Hilbert carrier
Hamiltonian and vacuum
connection to the finite Wilson approximants.
```

---

# Phase 20 — Physical OS/Wightman spectral gap and Clay-level completion

**Status: OPEN DOWNSTREAM / OPEN.**

After the full same-root physical continuum carrier is established, transfer the uniform finite-volume coercivity into a statement of the form

```text
spectrum(H_phys | Omega-perp) subset [m, infinity)
```

for some `m > 0`, or the correct equivalent formulation if the vacuum sector is not one-dimensional.

A Clay-level completion must combine, on one coherent same-root construction,

```text
4D continuum Yang--Mills existence
Euclidean covariance
reflection positivity / OS axioms in the required form
regularity / distributional field structure
physical nontriviality
correct vacuum structure
physical OS/Wightman Hilbert realization
strictly positive spectral gap above the vacuum sector.
```

Only after those obligations are discharged should the repository claim a complete Yang--Mills existence-and-mass-gap theorem.

---

# Parallel lane — SU(2) selected exact mode

**Status: Parallel.**

The selected exact-mode route seeks an attained positive-energy mode from raw Wilson data. It is useful but logically different from the twelve-block Poincare program.

Permanent distinction:

```text
one selected exact positive mode
  != lower spectral bound for the whole physical orthogonal sector.
```

Do not substitute exact-mode realization for the global coercivity theorem.

---

# Diagnostic lane — finite-volume Dobrushin / influence control

**Status: Diagnostic only for the continuum-gap question.**

The repository contains explicit finite-volume Wilson/Dobrushin information. Such bounds remain useful for local conditional-law dependence and may enter a block argument.

However simple influence coefficients that approach `1` in the relevant large-coupling regime cannot by themselves be presented as a final scale-independent continuum-gap proof.

This obstruction motivates stronger ground-state / block / geometry-aware coercivity rather than invalidating the program.

---

# Immediate execution order

```text
1. consume #3921/#3926 and prove the genuine one-link condExpL2 residual
   inequality on the actual ground-state joint carrier;
2. integrate the a.e. split-fiber estimate over outer contexts while
   preserving the sharp exp(-16 beta) factor whenever possible;
3. aggregate genuine one-link residuals to one spatial color block using
   the actual matching/disjoint-update geometry;
4. prove corresponding right-six and left-six block estimates;
5. combine them into quantitative twelve-block Dirichlet control;
6. identify the exact twelve-block common-fixed sector relevant to physical
   top-orthogonal right-boundary lifts;
7. prove a positive finite-volume twelve-block Poincare coefficient;
8. make the coefficient scale-independent or prove precisely where the
   proposed coefficient degenerates;
9. invoke the already-integrated E12 -> E6 -> raw defect -> transfer-gap route;
10. propagate the resulting uniform physical gap through a same-root
    thermodynamic / continuum construction.
```

This order avoids reopening solved local analysis and keeps the proof attached to the actual ground-state joint probability law.

---

# Definition of success for the present milestone

The current local-to-block milestone is complete only when Lean contains a theorem chain of the form

```text
sharp continuous-vacuum one-link variance
  + a.e. actual joint-fiber compatibility
  -> a.e. actual split-fiber variance                         [DONE]
  -> genuine joint one-link condExpL2 residual inequality     [NEXT]
  -> spatial color-block residual inequality                  [OPEN]
  -> quantitative twelve-block Dirichlet control              [OPEN].
```

The next major mass-gap milestone is complete only when that chain further yields

```text
actual ground-state twelve-block dynamics
  -> identified common-fixed sector
  -> exists kappa_* > 0 uniformly across the physical scaling family
  -> physical transfer gap >= 3 kappa_*/4.
```

Until the uniform model-derived coefficient and its same-root continuum propagation are proved, the global Yang--Mills mass-gap boundary remains open.