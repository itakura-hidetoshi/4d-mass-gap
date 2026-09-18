# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-18 JST**.

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The exact merged theorem-carrier baseline used for this refresh is

```text
9fbe314d4245c19fffa5762f8de683d3ab7d35fe
```

with tree

```text
8bb7d9e4928b132256dae655fea73e0620986397
```

This commit merges PR #4421:

```text
Descend two-step terminal response to aggregate left variation mass
```

The SHA printed here is documentation history, not live authority. The theorem-carrier branch must be fresh-fetched before theorem work.

Authority order remains:

```text
1. exact current GitHub theorem-carrier SHA
2. Lean theorem artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

`main` is not theorem authority when histories differ.

---

# Dependency graph

```text
A. FINITE PERIODIC WILSON / OS ROOT                           [INTEGRATED]
   -> compact SU(N) finite lattice
   -> reflection positivity
   -> transfer and ground-state structure
   -> conditional-expectation / coercivity interfaces

B. SAME-ROOT SCALAR CONTINUUM OS LANE                        [INTEGRATED]
   -> scalar readout limits
   -> continuum reflection positivity
   -> OS Hilbert carrier / C0 semigroup / Hamiltonian

C. CONTINUOUS C5 ONE-LINK LAW                                [INTEGRATED]
   -> normalized measurable SU(N) fiber law
   -> exact reinsertion
   -> off-target represented-source cancellation
   -> surviving q(beta)

D. LOCAL C5 GEOMETRY                                         [INTEGRATED]
   -> intrinsic spatial plaquette-neighbor degree <= 18
   -> exceptional set <= 20
   -> remote raw Wilson cancellation

E. FIXED-RIGHT GROUND-STATE RESPONSE                         [INTEGRATED]
   -> positive kernel-section probability law
   -> right update as normalized tilt
   -> two-source crossing response
   -> literal target-ratio response

F. PHYSICAL RESTRICTED-SCAN TRANSPORT                        [INTEGRATED]
   -> deterministic schedules
   -> restricted random scan over Sum.inl only
   -> finite-step expectation iterate
   -> tagged physical variation propagation

G. REMOTE TARGET-RATIO AGGREGATION                           [INTEGRATED]
   #4399 source-coordinate aggregate identity
   #4403 pointwise aggregate support
   #4406 all-coordinate finite superposition
   #4409 one-step represented-source aggregate response = 0

H. FIRST NONTRIVIAL AGGREGATE TRANSPORT                      [INTEGRATED]
   #4412 exact one-step left carrier
   #4415 exact first nonzero two-step right-source response
   #4418 volume-independent two-step right-source transport bound

I. TWO-STEP TERMINAL DESCENT                                 [INTEGRATED]
   #4421 continuous-state finite-coordinate telescoping
   #4421 probability expectation difference <= 2 * total variation
   #4421 two-step terminal remote column
         <= 2 * aggregate propagated left total mass

J. ARBITRARY-STEP TERMINAL / RESPONSE REDUCTION              [ACTIVE DRAFT]
   #4433 targetwise n-step terminal descent
   -> remote target summation
   -> full remote response column
      <= aggregate right-source term
       + 2 * aggregate left-total-mass term
   [NOT AUTHORITY UNTIL MERGED]

K. UNIFORM AGGREGATE LEFT-MASS CLOSURE                       [OPEN NOW]
   control
     sum_e Q^n(RemoteAggregateVariation)(Sum.inl e)
   without dense all-links volume growth

L. TARGET-INDEXED WORST-CASE RESPONSE FAMILY                 [OPEN NEXT]
   allow g1,g2,h,k to depend on target
   -> match genuine Dobrushin column quantifiers
   -> preserve one aggregate RHS

M. RESPONSE -> PHYSICAL REMOTE INFLUENCE                     [OPEN NEXT]
   normalization-aware response/cross-ratio comparison
   -> remote influence profile
   -> volume-uniform remote column rho

N. EXCEPTIONAL + REMOTE GATE                                 [INTEGRATED INTERFACE]
   exceptional <= 20*eta
   remote <= rho
   -> column <= 20*eta + rho
   -> strict contraction if 20*eta + rho < 1

O. CONTINUOUS RESPONSE CERTIFICATE / RESOLVENT               [OPEN DOWNSTREAM]
   concrete physical discrepancy/sourceBound witnesses
   -> existing certificate constructor
   -> source resolvent / sweep algebra

P. PHYSICAL POINCARE / COERCIVITY                            [OPEN DOWNSTREAM]
   strict physical response control
   -> conditional variance / block coercivity
   -> Poincare-type estimate

Q. UNIFORM FINITE-VOLUME TRANSFER GAP                        [OPEN DOWNSTREAM]
   volume-independent coercive constant
   -> physical transfer / Hamiltonian spectral gap

R. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                  [OPEN DOWNSTREAM]
   tight compatible finite-volume physical states
   -> limiting physical carrier / field content
   -> OS/Wightman spectral lower bound

S. CLAY-LEVEL EXISTENCE + MASS GAP                           [OPEN]
```

---

# Phase 0 — Authority, CI, and proof discipline

**Status: Integrated and permanent.**

For theorem-bearing work:

```text
fresh-fetch authoritative theorem-carrier branch
-> lock exact canonical SHA
-> inspect exact theorem interfaces
-> state the smallest coherent theorem unit
-> run exact-head CI
-> inspect the first genuine Lean error if RED
-> make the smallest proof-preserving fix
-> require completed/success for exact head
-> merge against expected exact head
-> fresh-fetch canonical again.
```

Queued or in-progress CI is not GREEN.

GitHub completion comments are wake-up signals only. They are not CI truth, merge authority, or write authority. Direct fresh observation of the exact workflow run and exact head SHA remains authoritative.

No new `sorry`, `admit`, axioms, hidden constants, assumption weakening, theorem weakening, or semantic broadening may be introduced as a substitute for proof.

---

# Phase 1 — Finite Wilson root and OS infrastructure

**Status: Integrated.**

The repository contains the finite periodic compact-`SU(N)` Wilson model, lattice geometry, Haar reference measure, Wilson action, reflection-positive structures, one-slab transfer operators, nonnegative ground-state architecture, conditional-expectation carriers, and downstream coercivity interfaces.

This is the finite theorem root. It is not itself a continuum Yang--Mills existence theorem.

---

# Phase 2 — Same-root scalar continuum OS lane

**Status: Integrated as a scalar observable lane.**

The repository also contains a same-root scalar continuum construction:

```text
finite Wilson scalar readout
-> continuum scalar law
-> continuum reflection positivity
-> OS Hilbert carrier
-> strongly continuous contraction semigroup
-> self-adjoint Hamiltonian / vacuum structure.
```

Boundary: this scalar lane is not yet the full four-dimensional Yang--Mills field/state required for the final problem.

---

# Phase 3 — Continuous C5 one-link law and local geometry

**Status: Integrated.**

The continuous C5 one-link law is a genuine normalized `SU(N)` probability kernel.

For represented right-boundary sources:

```text
source != resampled fiber
-> normalization cancels the source-dependent scalar exactly
-> represented influence = 0.
```

For the matching source:

```text
q(beta)
  = 2 * (exp(16*beta)-1)/(exp(16*beta)+1).
```

For

```text
0 <= beta < log 3 / 16,
```

one has `q(beta) < 1`.

The bare spatial Wilson geometry is bounded degree:

```text
intrinsic spatial plaquette-neighbor degree <= 18
C5 exceptional set size <= 20.
```

This bounded geometry is a central resource for the current sparse/local closure problem.

---

# Phase 4 — Fixed-right probability and response identities

**Status: Integrated.**

The continuous physical ground-state kernel section is normalized to a probability law.

The exact response chain is:

```text
ground-state kernel section
-> positive finite normalization
-> right update as normalized local Boltzmann tilt
-> covariance response
-> two-source crossing response
-> literal target-ratio specialization
-> remote reference law = source-then-target fixed-right kernel-section law
-> remote C5 covariance = fixed-right target-ratio response.
```

No decay is asserted by these identities.

---

# Phase 5 — Physical restricted-scan transport

**Status: Integrated.**

The actual C5 scan is represented on a tagged carrier:

```text
Sum.inl e  = physical left link
Sum.inr s  = represented right source.
```

Only `Sum.inl` coordinates are scan targets.

The repository formalizes:

```text
one-link expectation transport
-> deterministic schedules
-> restricted random scan
-> finite-step expectation iterate
-> physical fiber-variation propagation
-> represented-source transport.
```

The target-ratio observable has singleton initial physical variation

```text
exp(16*beta) at target,
0 elsewhere.
```

This avoids a volume-wide initial variation profile.

---

# Phase 6 — Remote aggregate variation

**Status: Integrated through #4409.**

Define the remote aggregate target-ratio variation by summing singleton target profiles over the remote C5 target set.

The merged formalization proves:

```text
#4399
  source-coordinate aggregate finite-superposition identity

#4403
  exact pointwise profile:
  exp(16*beta) on remote target fibers, zero elsewhere

#4406
  for every tagged coordinate e and every n:
  Q^n(RemoteAggregateVariation)(e)
    = sum_remote Q^n(singleton_target_variation)(e)

#4409
  one restricted-scan step cannot yet reach the represented source:
  Q(RemoteAggregateVariation)(Sum.inr source) = 0.
```

This exact superposition is the key algebraic step that permits remote-column summation before estimates are imposed.

---

# Phase 7 — First nontrivial aggregate transport

**Status: Integrated through #4418.**

## 7.1 Exact one-step left carrier — #4412

The first physical-left carrier generated by the remote aggregate profile is computed exactly.

Its finite-volume normalization appears as

```text
remote.card / card(Link),
```

not as a naked remote cardinality.

## 7.2 Exact first nonzero right-source response — #4415

The represented source is not reached at one step. At two steps the first nonzero response is computed exactly.

This proves the concrete route

```text
remote target
-> physical left fiber
-> represented right source.
```

## 7.3 Uniform two-step right-source transport — #4418

The remote set is embedded into the complete non-source two-step column, all summands are nonnegative, and the already-established full two-step column bound is reused.

The resulting represented-source transport term is volume-independent.

This closes the transport half of the two-step stationary residual.

---

# Phase 8 — Two-step terminal descent

**Status: Integrated through #4421.**

The previous terminal term was a difference of expectations of one common two-step-smoothed target-ratio observable under two fixed-right probability laws.

PR #4421 introduces the required continuous-state telescoping machinery.

## 8.1 Continuous-value finite-coordinate telescoping

For a finite coordinate carrier and arbitrary coordinate value type `G`:

```text
coordinate update bound:
  |f(update C e u) - f(update C e v)| <= variation(e)

implies

  |f(A) - f(B)| <= sum_e variation(e).
```

No `Fintype G` assumption is used. This is essential for `SU(N)`.

## 8.2 Arbitrary probability measures

The current generic expectation theorem gives

```text
|E_mu f - E_nu f|
<= 2 * sum_e variation(e)
```

for arbitrary probability measures on the finite coordinate carrier.

The factor `2` is safe and proof-complete. It is not currently claimed to be sharp.

## 8.3 Application to the two-step terminal response

The two-step smoothed target-ratio observable has physical-coordinate variation bounded by the two-step tagged iterate.

Therefore

```text
TerminalResponseAbs(target,source)
<= 2 *
   sum_e Q^2(variation_target)(Sum.inl e).
```

Summing over remote targets and commuting the finite sums via #4406 yields

```text
TerminalRemoteColumn
<= 2 *
   sum_e Q^2(RemoteAggregateVariation)(Sum.inl e).
```

The stationary terminal has thus been converted from an opaque measure discrepancy into a concrete aggregate propagated-left-mass obstruction.

---

# Phase 9 — Arbitrary-step terminal descent

**Status: Active draft; not theorem authority.**

Draft PR #4433 is extending Phase 8 from the fixed depth `2` to arbitrary `n`.

The intended target is:

```text
NStepTerminalRemoteColumn
<= 2 *
   sum_e Q^n(RemoteAggregateVariation)(Sum.inl e),
```

combined with the already-proved arbitrary-step remote residual decomposition to obtain

```text
RemoteResponseColumn
<= Q^n(RemoteAggregateVariation)(Sum.inr source)
   + 2 *
     sum_e Q^n(RemoteAggregateVariation)(Sum.inl e).
```

Until #4433 merges GREEN, these formulas are development targets, not canonical theorem claims.

---

# Phase 10 — Uniform aggregate-left-mass closure

**Status: OPEN NOW.**

This is the main quantitative obstruction after #4421.

The quantity to control is

```text
sum_{physical e}
  Q^n(RemoteAggregateVariation)(Sum.inl e).
```

A direct use of the generic dense distinct-fiber coefficient produces a term comparable to

```text
(card Link - 1) * offFiberInfluence(beta),
```

which reintroduces volume growth.

That route is therefore insufficient for the desired uniform column estimate.

A valid proof must instead exploit additional structure already present in the repository, for example:

```text
bounded local Wilson degree <= 18,
exceptional-set support <= 20,
exact remote target support,
exact fixed-right response identities,
normalization cancellation,
finite-step tagged transport,
response / residual recursion that is independently established.
```

The proof must remain non-circular.

---

# Phase 11 — Target-indexed worst-case response family

**Status: OPEN NEXT.**

The current remote response-column definitions use one common tuple

```text
g1, g2, h, k
```

for all remote targets.

A genuine Dobrushin column estimate must allow the worst-case group values to vary with the target. The next robust interface should therefore admit functions such as

```text
g1(target), g2(target), h(target), k(target)
```

or an equivalent supremum-compatible family.

The existing targetwise finite-step bounds are independent of the chosen values, so the planned strengthening should preserve the same aggregate tagged right-hand side.

This is a quantifier-strengthening step, not a new decay assumption.

---

# Phase 12 — Response to physical remote influence

**Status: OPEN NEXT.**

After a target-indexed response family is available, the next task is to convert fixed-right response size into the actual physical remote influence coefficient.

The repository already contains normalization-aware ingredients:

```text
positive local-factor ratios,
continuous-vacuum Harnack bounds,
Doob weighted-measure cross-ratio comparison,
cross-ratio influence transforms,
log(1+x) linearization:
  influenceTransform(log(1+x)) <= x.
```

A promising route is to derive a targetwise multiplicative residual of the form

```text
1 + const(beta) * response(target,source)
```

and then use the existing logarithmic influence transform so that the resulting physical influence is linear in the proved response rather than a uniform constant summed over all remote targets.

This route is **not yet a theorem**. It is the current normalization-aware bridge to investigate.

---

# Phase 13 — Concrete volume-uniform remote column rho

**Status: OPEN.**

The target is

```text
sup_source
  sum_{remote target}
    physicalRemoteInfluence(target,source)
<= rho
```

with `rho` independent of periodic volume.

The remote summation must be performed after the targetwise response has been tied to a summable aggregate quantity. A target-independent pointwise constant is not sufficient.

---

# Phase 14 — Exceptional plus remote strict-contraction gate

**Status: Integrated interface; physical constants open.**

The geometric decomposition already gives

```text
exceptional contribution <= 20 * eta
remote contribution <= rho
```

and hence

```text
columnSum <= 20 * eta + rho.
```

The first decisive continuous-`SU(N)` contraction milestone is a concrete parameter regime satisfying

```text
20 * eta + rho < 1.
```

Until this inequality is established with physical witnesses, the repository should not describe the continuous physical C5 lane as globally contractive.

---

# Phase 15 — Continuous response certificate and resolvent/sweep closure

**Status: OPEN DOWNSTREAM.**

The repository already contains state-space-independent response-certificate and source-resolvent interfaces.

Once a strict physical column estimate and concrete discrepancy/source-bound witnesses are available:

```text
physical response witnesses
-> response certificate
-> source resolvent
-> sweep comparison
-> quantitative response closure.
```

The generic algebra is not the present bottleneck. The bottleneck is the continuous physical witness with volume-independent constants.

---

# Phase 16 — Physical Poincare and coercivity

**Status: OPEN DOWNSTREAM.**

The intended route is

```text
strict continuous physical response control
-> block / conditional variance estimate
-> physical Poincare or coercivity inequality
-> volume-uniform control of the transfer sector.
```

This must use actual continuous `SU(N)` data. Z2-only decay results or abstract uninstantiated coefficients are not substitutes.

---

# Phase 17 — Uniform finite-volume transfer gap

**Status: OPEN DOWNSTREAM.**

The required target is a scale-independent constant

```text
kappa_* > 0
```

that produces a finite-volume physical transfer/Hamiltonian spectral lower bound uniform over the periodic volumes used in the limiting construction.

A gap whose constant collapses with volume is insufficient.

---

# Phase 18 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After a uniform finite-volume physical gap is established, the remaining program includes:

```text
compatible limiting physical states
-> same-root OS/Wightman carrier
-> limiting semigroup / Hamiltonian
-> sufficiently rich nontrivial 4D Yang--Mills field/state
-> spectral lower bound above the vacuum.
```

The existing scalar continuum OS lane is valuable same-root infrastructure, but it is not by itself the complete gauge-field construction required here.

---

# Phase 19 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The present repository contains a large formal proof spine and an increasingly concrete quantitative continuous-`SU(N)` response program, but the final claim boundary remains open until finite-volume uniformity, physical field content, limiting construction, and spectral obligations are all discharged.

---

# Immediate theorem-development checklist

Starting from merged theorem baseline #4421:

```text
1. finish arbitrary-n terminal descent and merge only after exact-head GREEN;

2. derive the full arbitrary-n remote response reduction to
   aggregate right-source + aggregate physical-left mass;

3. strengthen the response column to target-indexed worst-case SU(N) values;

4. formalize the sharpest normalization-aware response-to-influence bridge;

5. derive a sparse/local recursion or support-sensitive estimate for
   the aggregate physical-left mass without the dense all-links majorant;

6. prove a volume-uniform remote column rho;

7. combine rho with the exceptional contribution 20*eta;

8. establish a concrete regime 20*eta + rho < 1;

9. instantiate the existing response certificate / source resolvent / sweep
   machinery with the actual continuous physical witnesses;

10. derive physical Poincare/coercivity and a volume-uniform finite-volume gap;

11. only then advance the thermodynamic/continuum physical Yang--Mills limit.
```

The conceptual transition is now:

```text
#4367:
  exact fixed-right stationary finite-step response residual

#4406:
  exact remote aggregate superposition at every tagged coordinate

#4418:
  volume-independent first nontrivial aggregate represented-source transport

#4421:
  terminal response converted to aggregate propagated physical-left mass

current frontier:
  prove that aggregate propagated left mass and the induced physical response
  are uniformly summable in volume.
```
