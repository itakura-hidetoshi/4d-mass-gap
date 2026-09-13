# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-13 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest mathematical baseline before this documentation refresh is

```text
697591e7984f96f07ed0acfbd709b0df301affbe
```

which is the normal merge of PR #4030,

```text
Bridge reference one-link normalization to singleton marginals
```

with exact theorem head and validation

```text
head:
  cf3ae6954150824c804959089f2a096aa5495ea9

PR Lean Fast Check #13744
workflow run 34753572564
completed / success
```

The public `main` branch is a landing surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status. Documentation-only merges may advance the branch pointer without changing the mathematical baseline stated above.

> **Current frontier**
>
> The old frontier at actual split-fiber variance and genuine one-link `condExpL2` residuals has been crossed on the bounded concrete core. The repository also contains a formal obstruction to naive same-color summation: a uniform nonzero remote influence coefficient accumulates a link-count factor.
>
> The active proof route therefore isolates the true remote dependence. Raw same-color Wilson locality gives exact cancellation, while the continuous-vacuum integration layer converts the remaining physical cross-ratio defect into a covariance between a target-local and a source-local observable under a genuine normalized reference probability law.
>
> PRs #4019--#4030 construct the exact one-link fiber, singleton marginal, normalized fiber density, base-point invariance, and fiber normalization identity for that reference law. The immediate next theorem is **full normalized reference-law one-link heat-bath / Fubini compatibility**. Only after that should a measurable conditional-law / RCD theorem and a summable covariance or influence estimate be attempted.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated on bounded core** — theorem is canonical on the explicit dense bounded concrete core; no arbitrary-`L²` pointwise statement is implied.
- **Integrated routing** — implication chain is formalized, but a model-derived quantitative input is still missing.
- **Obstruction integrated** — a rigorous negative/insufficiency result rules out a tempting route.
- **Open now** — immediate constructive frontier.
- **Open next** — next coherent unit after the current frontier.
- **Open downstream** — required later in the global gap route.
- **Parallel** — independent proof lane that must not be substituted for global coercivity.

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
  -> 6 right + 6 left genuine spatial condExp projections            [Integrated]
  -> genuine 12-spatial family                                      [Integrated]
  -> E12 -> E6 -> raw physical defect -> transfer gap                [Integrated routing]

D. SHARP DIRECT ONE-LINK CONTROL

continuous-vacuum complete one-link weight                           [#3894]
  -> exp(16 beta) Harnack                                             [Integrated]
  -> sharp normalized Haar comparison                               [#3898]
  -> exp(-16 beta) one-link variance lower bound                     [#3907]
  -> a.e. actual joint split-fiber compatibility                     [#3909]
  -> actual split-fiber variance / residual transfer                 [#3921, #3926]

E. GENUINE JOINT condExpL2 BRIDGE

weighted outer-context integration                                  [#3934]
  -> outer-centered residual                                         [#3936]
  -> condExpL2 outer representative                                  [#3937]
  -> bounded concrete one-link sections                              [#3938]
  -> genuine joint L2 residual norm                                  [#3942]
  -> dense bounded concrete core                                     [#3949]
  -> all spatial links / color residual domination                   [#3952]
                                                                     [Integrated on bounded core]

F. SAME-COLOR REMOTE-INFLUENCE DIAGNOSTICS

remote weight distortion exp(8 beta)                                [#3954]
  -> normalized Doob comparison exp(16 beta)                         [#3959]
  -> bounded-test influence                                          [#3964]
  -> naive row majorant = link-count x single-source coefficient     [#3969]
                                                                     [Obstruction integrated]

G. RAW LOCALITY AND COVARIANCE LOCALIZATION

raw same-color local-factor cancellation                             [#3978]
  -> raw kernel cross-ratio K = 1                                    [Integrated]
  -> continuous-vacuum integral normal form                          [#3983]
  -> source likelihood ratio is source-link local                    [#3991, #3994]
  -> four-integral defect = weighted covariance                      [#3997, #4000]
  -> target-local x source-local covariance                          [#4004]
                                                                     [Integrated]

H. NORMALIZED CONTINUOUS-VACUUM REFERENCE LAW

canonical positive reference weight                                 [#4011]
  -> normalized probability law                                     [#4016]
  -> physical defect = scalar x Z^2 x Cov_nu_ref                    [#4016]
  -> literal one-link fiber probability                              [#4019]
  -> fiber partition = singleton marginal                            [#4024]
  -> normalized fiber density / base-point invariance                [#4027]
  -> marginal x fiber expectation = weighted marginal                [#4030]
                                                                     [Integrated]

I. FULL-LAW CONDITIONAL SPECIFICATION

#4030 local normalization identity
  -> normalized full-law heat-bath / Fubini invariance               [OPEN NOW]
  -> measurable one-link heat-bath Markov kernel                     [OPEN NEXT]
  -> RCD / conditional-expectation identification, if justified      [OPEN NEXT]

J. SUMMABLE REMOTE MIXING

conditional specification
  -> distance-sensitive covariance / influence bound                 [OPEN]
  -> same-color row sum bounded independently of volume              [OPEN]
  -> one spatial color-block coercivity                              [OPEN]

K. GLOBAL FINITE-VOLUME COERCIVITY

six right + six left block estimates                                [OPEN]
  -> quantitative E12 control                                        [OPEN]
  -> relevant common-fixed sector                                    [OPEN]
  -> model-derived kappa(H,N,beta) > 0                              [OPEN]
  -> scale-independent kappa_* > 0                                  [OPEN]
  -> physical transfer gap >= 3 kappa_*/4                            [Integrated routing]

L. THERMODYNAMIC / CONTINUUM PROPAGATION

uniform finite-volume physical transfer gap                          [OPEN DOWNSTREAM]
  -> stable Green / resolvent / Poincare control                     [OPEN DOWNSTREAM]
  -> thermodynamic / scaling-limit physical carrier                  [OPEN DOWNSTREAM]
  -> physical OS/Wightman spectral lower bound                       [OPEN DOWNSTREAM]

M. CLAY-LEVEL COMPLETION

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
separate missing-.olean / cache diagnostics from genuine Lean errors
inspect the first genuine terminal Lean failure before editing
keep theorem development additive / tighten-only
never strengthen assumptions merely to make elaboration easier
forbid proof placeholders in theorem source
merge with expected head SHA fixed
verify merge parents and the canonical branch pointer
```

Claim discipline:

```text
finite theorem != continuum theorem
positive coefficient at each scale != uniform positive coefficient
local Harnack / Doeblin / variance != global L2 Poincare
bounded-core theorem != arbitrary-L2 pointwise theorem
literal normalized fiber != RCD
heat-bath invariance != quantitative mixing
uniform pairwise remote bound != summable row bound
raw Wilson K = 1 != continuous-vacuum Doob K = 1
covariance localization != covariance decay
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

Permanent rule: keep the interacting Wilson model visible through every decisive physical bridge. Product Haar is a reference measure only through explicit comparison, marginal, split-coordinate, and pushforward theorems.

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

The fixed-finite-volume program contains:

```text
physical top/non-top decomposition
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

This is downstream infrastructure. The active program seeks a model-derived, scale-controlled source of coercivity from the actual ground-state conditional dynamics.

---

# Phase 4 — Ground-state joint law and genuine twelve-spatial dynamics

**Status: Integrated.**

The authoritative branch contains:

```text
strictly positive physical ground-state structure
ground-state normalized one-slab law
genuine left/right joint probability measure
left/right boundary L2 isometries
coarse conditional-expectation / Doob boundary geometry
6 genuine right spatial conditional expectations
6 genuine left spatial conditional expectations
explicit two-sided 12-spatial family
qualitative common-fixed characterization
```

The physical implication chain is already canonical:

```text
12-block Poincare coefficient kappa
  -> six-spatial frame coefficient 2 kappa
  -> physical transfer gap >= 3 kappa / 4.
```

This is integrated routing. It does not supply `kappa`.

---

# Phase 5 — Complete continuous-vacuum one-link Harnack and normalized variance

**Status: Integrated through PRs #3894, #3898, #3907.**

For the complete direct one-link weight `Wc`, the authoritative branch proves

```text
0 < Wc(g)
Wc(g) <= exp(16 * beta) * Wc(h).
```

With

```text
mu  = normalized compact Haar on SU(N)
Z   = integral Wc dmu
rho = Wc / Z
nu  = rho * mu
R   = exp(16 * beta),
```

it proves

```text
0 < Z < infinity
R^{-1} <= rho(g) <= R
R^{-1} mu <= nu <= R mu
R^{-1} * evariance_mu(X) <= evariance_nu(X).
```

The normalized comparison pays the Harnack factor once; no artificial `exp(-32 * beta)` degradation is introduced.

Completion criterion: satisfied.

---

# Phase 6 — Bridge the direct law to the actual joint split fiber

**Status: Integrated through PRs #3909, #3921, #3926.**

The direct continuous-vacuum law and the legacy ground-state joint density use vacuum representatives that agree only almost everywhere. The correct bridge is therefore a.e.

The integrated route:

```text
reconstruct complete right boundary from retained off-target coordinates
transport Omega_cont = Omega a.e. through the exact target/off-target split
identify normalized split target fibers for a.e. outer context
prove exact singleton-target Measure.map transport back to SU(N)
transfer fixed-center / best-center / evariance bounds
transport evariance through target-evaluation IdentDistrib
preserve exp(-16 * beta) on the actual split fiber.
```

Permanent constraints:

```text
no arbitrary quotient representative pointwise evaluation
no promotion of a.e. equality to universal equality
no implicit RCD identification
no extra Harnack loss.
```

Completion criterion: satisfied.

---

# Phase 7 — Integrate the actual split-fiber estimate into genuine `condExpL2`

**Status: Integrated on the bounded concrete core through PRs #3934--#3952.**

This phase replaces the former README frontier.

The canonical sequence is:

```text
#3934
  multiply the a.e. split-fiber variance by the genuine target-fiber mass
  and integrate over left and retained off-target contexts.

#3936
  bound that variance by a centered residual whose center may depend on
  the complete outer context.

#3937
  identify the one-link conditioning sigma-algebra with the retained
  outer-context pullback and use Doob--Dynkin to obtain a measurable
  representative of genuine condExpL2.

#3938
  use bounded strongly measurable concrete observables so every direct
  Haar target section is genuinely MemLp 2 and insert the condExp center.

#3942
  identify the weighted centered nested integral with
  ENNReal.ofReal ||f - condExpL2 target f||^2 on the actual joint law.

#3949
  define the bounded concrete joint L2 core and prove it is dense using
  Lp.simpleFunc.dense.

#3952
  choose one common bounded representative across all spatial targets and
  dominate each genuine one-link residual by the residual of the spatial
  color block containing that target.
```

What is canonical now:

```text
sharp model-derived one-link information
  -> genuine joint condExpL2 residual on bounded concrete core
  -> per-target domination by genuine color residual.
```

What is **not** claimed:

```text
arbitrary-L2 pointwise fiber sections
RCD identification
volume-independent color-block coercivity from naive summation.
```

Completion criterion: local bounded-core bridge satisfied. Globalization remains open.

---

# Phase 8 — Quantify remote same-color influence and prove the naive row-sum obstruction

**Status: Integrated / obstruction integrated through PRs #3954--#3969.**

The repository proves the model-facing chain

```text
same-color remote pointwise weight comparison
  factor R = exp(8 * beta)                                  [#3954]

normalized remote one-link Doob laws
  mutual domination factor R^2 = exp(16 * beta)             [#3959]

bounded measurable |phi| <= 1
  |E_mu phi - E_nu phi|
    <= 2 * (K - 1) / (K + 1), K = exp(16 * beta)            [#3964].
```

PR #3969 formalizes the finite remote source set in one same-color class and the naive constant-majorant row sum. That majorant is exactly the number of remote sources times the single-source coefficient.

Therefore

```text
uniform positive influence per remote source
  != volume-independent Dobrushin contraction.
```

This is not a failure of locality. It is a proof that a constant pairwise bound is too coarse for globalization.

Completion criterion: obstruction identified and canonical.

---

# Phase 9 — Recover the exact raw locality hidden by continuous-vacuum integration

**Status: Integrated through PRs #3974--#3994.**

The normalized cross-ratio comparison API is available generically (#3974), and the continuous-vacuum coarse cross-ratio is packaged (#3976). The crucial model result is sharper:

PR #3978 proves exact same-color remote locality for the **raw one-slab Wilson kernel**:

```text
remote source update leaves the distinct same-color target-local factor unchanged
raw four-point kernel cross-ratio = 1.
```

This must not be lifted directly to the continuous physical vacuum. The integration against the vacuum representative is exactly where nonlocal dependence may re-enter.

The later integrated normal forms isolate that dependence:

```text
#3983
  continuous-vacuum value = left-boundary integral with target-local factor
  separated from the remote-source-updated base kernel.

#3986
  generic pairwise cross-ratio bounds can be transported through integration
  without coefficient worsening when such an all-pairs bound is available.

#3991
  the source-conditioned raw kernel left-boundary cross-ratio is source-local.

#3994
  the source likelihood ratio factors as
  A-independent right-boundary scalar x one-link Wilson crossing ratio.
```

The conclusion is structural: target-source distance does not appear in the raw same-color identity. Any genuine decay must be produced by the left-boundary correlation layer.

Completion criterion: exact locality surface identified.

---

# Phase 10 — Localize the physical remote defect as covariance

**Status: Integrated through PRs #3997, #4000, #4004.**

PR #3997 introduces a generic real unnormalized weighted covariance numerator and proves the exact four-integral cross-ratio identity

```text
I(a p r) I(a q s) - I(a p s) I(a q r)
  = CovNum_{a q s}(p/q, r/s)
```

under pointwise denominator nonvanishing, without probability normalization or independence assumptions.

PR #4000 specializes this identity to the physical continuous-vacuum same-color remote interface.

PR #4004 combines the source-ratio localization from #3994 with scalar extraction to obtain

```text
physical remote four-point defect
  = source spatial scalar
    * CovNum_referenceWeight(target-local ratio, source-local crossing ratio).
```

The two covariance observables are now spatially localized at the target and source respectively.

Permanent distinction:

```text
covariance localization != covariance decay.
```

Completion criterion: satisfied.

---

# Phase 11 — Replace the covariance weight by a canonical positive continuous reference law

**Status: Integrated through PRs #4011 and #4016.**

PR #4011 defines the pointwise-positive canonical reference weight

```text
w_ref(A) = Omega_cont(A) * L_g2(A) * Q_k(A)
```

and proves the weighted covariance numerator is unchanged when the legacy `L²` vacuum representative is replaced by `Omega_cont` using an a.e. weight-congruence theorem.

PR #4016 then normalizes `w_ref`.

A key proof-engineering lesson is permanent: normalization does **not** require a full continuity theorem for the product. The proof uses only

```text
Omega_cont integrable
0 < L_g2 <= exp(8 * beta)
0 < Q_k <= 1
w_ref <= exp(8 * beta) * Omega_cont.
```

It proves

```text
Z_ref > 0
nu_ref = normalized probability law of w_ref
CovNum_w_ref(f,g) = Z_ref^2 * Cov_{nu_ref}(f,g).
```

Hence the physical remote defect is exactly

```text
source scalar * Z_ref^2 * Cov_{nu_ref}(target-local ratio, source-local ratio).
```

No Wilson-Gibbs identification is asserted.

Completion criterion: satisfied.

---

# Phase 12 — Build the literal one-link reference fiber and singleton marginal

**Status: Integrated through PRs #4019 and #4024.**

For a selected spatial coordinate `fiber` and background configuration `A`, PR #4019 defines

```text
w_fiber(A,g) = w_ref(A[fiber <- g])
```

and proves

```text
0 < w_fiber(A,g)
Haar-integrability
0 < Z_fiber(A)
normalized literal fiber probability nu_fiber(A).
```

The integrability proof deliberately avoids a heartbeat-heavy complete fiber-weight continuity theorem. It uses continuous/integrable vacuum factor plus measurable local factors and domination.

PR #4024 identifies the fiber normalizer with Mathlib's singleton marginal of the full ENNReal density `rho_ref = ENNReal.ofReal o w_ref`:

```text
ENNReal.ofReal Z_fiber(A)
  = lmarginal_{ {fiber} } rho_ref(A).
```

This is a genuine full-density / one-coordinate Fubini bridge, but still not an RCD theorem.

Completion criterion: satisfied.

---

# Phase 13 — Expose the exact normalized one-link density

**Status: Integrated through PR #4027.**

PR #4027 proves

```text
nu_fiber(A)
  = Haar.withDensity
      (g |-> rho_ref(A[fiber <- g]) /
        lmarginal_{ {fiber} } rho_ref(A)).
```

It also proves literal base-point invariance:

```text
changing A only at `fiber`
  leaves w_fiber, Z_fiber, and nu_fiber unchanged.
```

This is the correct conditional-density candidate. It depends only on the off-fiber context even though it is represented using a complete background configuration.

Permanent distinction:

```text
exact normalized density formula
  != measurable Markov kernel
  != RCD.
```

Completion criterion: satisfied.

---

# Phase 14 — Prove the exact fiber normalization identity

**Status: Integrated through PR #4030.**

For every nonnegative measurable full-configuration observable `F`, PR #4030 proves

```text
lmarginal rho_ref(A)
  * integral_g F(A[fiber <- g]) d nu_fiber(A)
= lmarginal (rho_ref * F)(A).
```

The proof explicitly uses

```text
m = singleton marginal = ENNReal.ofReal Z_fiber(A)
m != 0
m != infinity
nu_fiber = Haar.withDensity (rho_fiber / m)
lintegral_withDensity
m * m^{-1} = 1.
```

This is the local normalization / disintegration algebra needed before an outer Fubini theorem.

Completion criterion: satisfied.

---

# Phase 15 — Full normalized reference-law one-link heat-bath / Fubini compatibility

**Status: OPEN NOW — immediate frontier.**

The next theorem should integrate Phase 14 over the full background law and prove that resampling one coordinate from `nu_fiber(A)` preserves the normalized reference law.

Target form:

```text
integral_A
  [ integral_g F(A[fiber <- g]) d nu_fiber(A) ]
  d nu_ref(A)
=
integral_A F(A) d nu_ref(A)
```

for nonnegative measurable `F`, or an equivalent unnormalized identity from which this follows exactly.

Preferred proof route:

```text
1. start from the full spatial product Haar measure;
2. expand nu_ref as the normalized reference density;
3. apply singleton-coordinate Fubini / lmarginal machinery;
4. insert #4030 pointwise normalization identity;
5. use base-point invariance so the inner normalized fiber is genuinely
   an off-fiber-context quantity;
6. cancel the global normalization only after positive finite mass is explicit.
```

Critical constraints:

```text
do not call the fiber an RCD before proving the full-law compatibility
avoid unnecessary continuity assumptions
preserve the exact full reference density
do not identify nu_ref with the Wilson Gibbs law
keep ENNReal zero/top cancellation receipts explicit.
```

### Completion criterion

A canonical full-law lintegral / expectation identity proves exact one-coordinate heat-bath invariance for `nu_ref`.

---

# Phase 16 — Construct the measurable one-link heat-bath kernel and conditional-law bridge

**Status: OPEN NEXT.**

After Phase 15, package the family

```text
A |-> pushforward of nu_fiber(A) by g |-> A[fiber <- g]
```

as a measurable Markov kernel on full configurations, or use the existing generic measurable Doob-weighted Markov-kernel infrastructure if it specializes cleanly.

Required obligations are separate:

```text
measurability in the outer configuration
probability-kernel property
base-point / off-fiber-context invariance
full-law invariance from Phase 15
conditional-expectation or RCD identity on the retained sigma-algebra.
```

Do not infer an RCD merely because a normalized density exists pointwise.

### Completion criterion

A theorem states, with all measurable-space hypotheses explicit, that the one-link kernel is the correct conditional specification of `nu_ref` relative to the off-fiber sigma-algebra.

---

# Phase 17 — Derive summable target-source covariance / influence control

**Status: OPEN — principal quantitative frontier after Phase 16.**

The physical same-color remote defect is already localized to

```text
Cov_{nu_ref}(target-local ratio, source-local ratio).
```

The next quantitative objective is a bound whose spatial dependence is strong enough to sum over all same-color remote sources without volume growth.

Acceptable forms include

```text
|Cov_{nu_ref}(f_target, g_source)| <= C * a(distance(target,source))
with sum_source a(distance(target,source)) <= C_sum < infinity,
```

or an equivalent conditional-influence / block contraction theorem.

Possible methods may use the newly formalized one-link conditional specification, local Wilson geometry, Dobrushin-type iteration, block conditioning, or another rigorous mixing mechanism. The method is secondary; the required property is summability with explicit parameter dependence.

### Mandatory diagnostic

Every candidate estimate must be tested for

```text
volume dependence
beta dependence
lattice-spacing / scaling dependence
loss introduced by normalization
loss introduced by summing remote sites.
```

If the coefficient degenerates in the physical scaling regime, formalize that obstruction rather than hiding it behind a uniform hypothesis.

### Completion criterion

A canonical bound controls the full same-color remote row or equivalent covariance sum by a constant independent of the number of spatial links.

---

# Phase 18 — Convert summable remote control into one spatial color-block coercivity

**Status: OPEN DOWNSTREAM.**

Combine:

```text
bounded-core genuine one-link condExpL2 residual control from Phase 7
+ all-link/color residual domination from #3952
+ summable remote dependence from Phase 17
+ actual same-color matching / disjoint-update geometry
```

to derive one spatial color-block coercivity estimate without inverse-volume loss.

The proof must not simply sum one-link lower bounds with a coefficient proportional to the number of links. It must use the quantitative interaction structure proved in Phase 17.

### Completion criterion

A theorem on the actual ground-state joint carrier gives a model-derived, volume-controlled lower bound for the residual of one genuine spatial-color conditional expectation.

---

# Phase 19 — Assemble six-right and six-left block coercivity

**Status: OPEN DOWNSTREAM.**

Prove corresponding estimates for the six right spatial colors and six left spatial colors on the same genuine joint `L²` carrier.

Target:

```text
E12(z)
  = (1/12) sum over the 12 genuine spatial blocks ||z - P_c z||^2
  >= explicit model-derived coercive quantity.
```

The theorem must remain attached to the actual ground-state joint probability law.

---

# Phase 20 — Identify the relevant twelve-block common-fixed sector

**Status: OPEN DOWNSTREAM.**

The repository contains qualitative simultaneous-fixedness information. The next geometric theorem must identify the common-fixed sector strongly enough to place the physical top-orthogonal right-boundary lifts in the correct orthogonal complement.

Do **not** assert that the common-fixed space is constants unless the retained sigma-algebras and the actual joint law prove that statement.

### Completion criterion

A theorem identifies exactly the fixed sector needed by the block Poincare argument and relates it to the physical top/common sector without an independent assumption.

---

# Phase 21 — Prove a finite-volume twelve-block `L²` Poincare theorem

**Status: OPEN DOWNSTREAM.**

After Phases 18--20, prove

```text
kappa(H,N,beta) * ||z||^2 <= E12(z)
```

on the orthogonal complement of the identified common-fixed sector, with

```text
kappa(H,N,beta) > 0
```

derived from the actual model.

This must be a genuine `L²` coercivity theorem. Total-variation or influence control may support it but may not be silently substituted for it.

### Completion criterion

A model-derived positive finite-volume coefficient is proved on the genuine ground-state twelve-block dynamics.

---

# Phase 22 — Make the coefficient scale-independent

**Status: OPEN DOWNSTREAM — decisive quantitative milestone.**

A positive coefficient at each finite scale is not enough. Along the physical scaling family one needs

```text
exists kappa_* > 0, for every relevant scale n,
  kappa_* * ||z||^2 <= E12_n(z).
```

The coefficient must come from quantities whose volume, lattice-spacing, and coupling dependence are explicit.

Two acceptable outcomes:

```text
A. uniform coercivity succeeds
   -> retain an explicit kappa_* > 0;

B. the proposed coefficient degenerates
   -> prove the degeneration honestly;
   -> identify the losing estimate;
   -> replace it with stronger block / multiscale / geometry-aware control.
```

Never hide scale degeneration behind a uniform hypothesis.

---

# Phase 23 — Invoke the integrated physical transfer-gap route

**Status: Integrated routing; waiting for Phase 22 input.**

Once a uniform twelve-block coefficient exists, no new abstract gap architecture is needed. The canonical route gives

```text
uniform twelve-block Poincare kappa_*
  -> six-spatial frame coefficient 2 kappa_*
  -> raw physical squared-defect coercivity
  -> physical transfer gap >= 3 kappa_*/4.
```

The theorem work here should be specialization and carrier bookkeeping rather than a replacement proof architecture.

---

# Phase 24 — Uniform finite-volume analytic consequences

**Status: OPEN DOWNSTREAM.**

Feed the uniform physical gap into the already-integrated finite-volume machinery to obtain stable versions of

```text
non-top contraction / decay
coercivity
resolvent control
Green bounds
relative Poincare estimates
reduced-range control.
```

---

# Phase 25 — Thermodynamic and scaling-limit propagation

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

A uniform finite-volume inequality alone is not a continuum mass-gap theorem. The limiting physical carrier and operator must be constructed and identified.

---

# Phase 26 — Full same-root physical continuum carrier

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

# Phase 27 — Physical OS/Wightman spectral gap and Clay-level completion

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

# Immediate execution order

```text
1. prove full normalized-reference one-link heat-bath / Fubini compatibility
   from #4030 and singleton-coordinate product-Haar integration;

2. package the one-link resampling family as a measurable Markov kernel and
   prove the conditional-law / RCD bridge only after the required
   measurability and full-law compatibility are explicit;

3. derive a target-source covariance or influence estimate for the
   target-local / source-local observables appearing in #4016;

4. prove that the resulting same-color remote row is summable with a bound
   independent of the number of links; if it is not, formalize the exact
   parameter or scale obstruction before changing strategy;

5. combine that summable remote control with the canonical bounded-core
   genuine condExpL2 one-link residual layer to obtain one spatial color
   block without link-count loss;

6. prove six-right and six-left block estimates and assemble quantitative
   twelve-block Dirichlet control;

7. identify the exact twelve-block common-fixed sector relevant to physical
   top-orthogonal right-boundary lifts;

8. prove a positive finite-volume twelve-block Poincare coefficient and then
   make it scale-independent, or prove precisely where the coefficient
   degenerates;

9. invoke the already-integrated E12 -> E6 -> raw defect -> transfer-gap route;

10. propagate the resulting uniform physical gap through a same-root
    thermodynamic / continuum construction.
```

This order does not reopen solved one-link Harnack analysis. It uses the obstruction theorem #3969 to force the proof toward actual mixing/correlation structure, and it uses #4030 as the exact law-side bridge needed to make that structure accessible.

---

# Definition of success for the present milestone

The current conditional-specification milestone is complete only when Lean contains the chain

```text
normalized continuous-vacuum reference law                         [DONE]
  -> literal normalized one-link fibers                            [DONE]
  -> singleton marginal normalizer                                [DONE]
  -> exact normalized fiber density                               [DONE]
  -> local normalization identity                                 [DONE]
  -> full-law one-link heat-bath / Fubini invariance              [NEXT]
  -> measurable conditional specification / RCD bridge            [OPEN]
  -> summable target-source covariance or influence               [OPEN].
```

The next local-to-block milestone is complete only when that chain further yields

```text
summable same-color remote dependence
  + bounded-core genuine one-link condExpL2 coercivity
  -> volume-independent spatial color-block residual inequality
  -> quantitative twelve-block Dirichlet control.
```

The next major mass-gap milestone is complete only when

```text
actual ground-state twelve-block dynamics
  -> identified common-fixed sector
  -> exists kappa_* > 0 uniformly across the physical scaling family
  -> physical transfer gap >= 3 kappa_*/4.
```

Until the uniform model-derived coefficient and its same-root continuum propagation are proved, the global Yang--Mills mass-gap boundary remains open.