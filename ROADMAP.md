# MGAP4D Roadmap

This roadmap records the theorem architecture and development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-16 JST**.

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

with current exact canonical HEAD

```text
2ebe3ee4a69a662a2010d5e2a41ba1b1953289bc
```

and tree

```text
b87194cad77d5136d02797ca2a9a88689d9944d2.
```

This is the merge of PR #4266,

```text
Specialize restricted-target geometric residual to physical C5
```

from exact GREEN proof head

```text
7c9d0662a30fd8d0006553aa7215014e6f577093
```

validated by

```text
PR Lean Fast Check #13971
workflow run 35063053481
completed / success.
```

`main` remains a public landing surface, not theorem authority. The authority order is

```text
exact canonical SHA
-> formal Lean artifacts
-> README / ROADMAP
-> CI/runtime receipts
-> historical summaries or memory.
```

> **Current frontier**
>
> The old multi-step semantic gap is closed. The repository now contains an actual continuous-C5 restricted random-scan process, its finite-step physical expectation iterate, tagged variation domination, generic restricted-target geometric forcing residual, and the physical C5 specialization through PR #4266.
>
> The new obstruction is quantitative: the exact left-restricted physical column sum is
>
> ```text
> (card Link - 1) * offFiberInfluence(beta).
> ```
>
> Thus the finite-step residual is formalized, but no volume-uniform contraction follows from the present all-to-all off-fiber majorant. The immediate theorem-development target is therefore to sharpen the physical left-left support/coefficient structure before attempting a scale-independent response/coercivity theorem.

---

## Status legend

- **Integrated** — merged theorem/model result on the authoritative branch.
- **Integrated routing** — implication chain is formalized, but a quantitative physical input remains open.
- **Integrated conditional interface** — theorem is proved, but concrete witnesses must still be supplied.
- **Obstruction integrated** — a tempting route has been formally exposed as insufficient or semantically invalid.
- **Open now** — immediate theorem-development frontier.
- **Open next** — next coherent unit after the present frontier.
- **Open downstream** — required later in the global mass-gap route.

---

# Roadmap in one view

```text
A. FINITE WILSON / OS ROOT                                      [INTEGRATED]

periodic-even compact SU(N) Wilson model
  -> reflection geometry / OS positivity
  -> spatial-slice and boundary L2 carriers
  -> physical one-slab transfer / ground-state structure

B. SAME-ROOT SCALAR CONTINUUM OS                               [INTEGRATED]

finite Wilson scalar readout
  -> same-root continuum scalar probability law
  -> continuum reflection positivity
  -> OS Hilbert carrier / C0 semigroup / Hamiltonian

C. FINITE PHYSICAL CONDITIONAL / GAP ROUTING                   [INTEGRATED ROUTING]

ground-state joint law
  -> six-right + six-left spatial condExp projections
  -> twelve-spatial family
  -> Poincare/coercivity -> physical transfer-gap route

D. SHARP CONTINUOUS ONE-LINK CONTROL                           [INTEGRATED]

continuous-vacuum one-link law
  -> Harnack / normalized comparison
  -> one-link variance lower bound
  -> bounded-core conditional residual

E. RIGHT-BOUNDARY C5 EXACT LOCALITY                            [INTEGRATED]

right source != resampled fiber
  -> scalar multiple of common weight
  -> normalization cancellation
  -> normalized laws equal
  -> heat-bath kernels equal
  -> represented influence exactly zero

right source = resampled fiber
  -> q(beta) = 2*(exp(16 beta)-1)/(exp(16 beta)+1)
  -> row sum q(beta)
  -> beta < log 3/16 => q(beta) < 1

F. ONE-WAY RIGHT-BOUNDARY TAGGED CARRIER                       [INTEGRATED]

Sum.inl target <- Sum.inr source
  -> exact represented C5 coefficient
  -> structural zero elsewhere only as carrier semantics
  -> generic source-resolvent / sweep algebra

G. STATE-SPACE-INDEPENDENT RESPONSE INTERFACE                  [INTEGRATED INTERFACE]

FiniteKernelStationaryResponseFamilyCertificate
  -> discrepancy
  -> sourceBound
  -> variation profile
  -> finite-step residual witness
  -> source-summed response / resolvent machinery

H. ACTUAL CONTINUOUS ONE-LINK VARIATION REALIZATION            [INTEGRATED]

#4201 fiber-variation scaling
#4205 represented tagged coefficient
#4208 one generic target-update domination
#4211 full represented right-source row

I. PHYSICAL TWO-STEP LEFT-LEFT TRANSPORT                       [INTEGRATED]

#4217 same-fiber two-step propagation
#4220 explicit augmented left-left carrier / criterion
#4223 literal C5 off-fiber conditional-law comparison
#4237 assumption-free distinct-fiber two-step transport

J. DETERMINISTIC FINITE SCHEDULES                              [INTEGRATED]

#4242 generic finite schedule recursion
  -> tagged schedule representation
  -> continuous C5 physical schedule transport

K. RESTRICTED RANDOM-SCAN SEMANTICS                            [INTEGRATED]

#4249 generic restricted-target scan
#4252 actual physical continuous C5 restricted scan
#4254 one-step measurable affine transport
#4257 finite-step physical expectation iterate
       + left-variation domination
       + boundary-parameter transport domination

Only Sum.inl physical fibers are scan targets.
Sum.inr boundary-source coordinates are not scanned.

L. RESTRICTED GEOMETRIC FORCING RESIDUAL                       [INTEGRATED]

#4260 generic Sum tau sigma left restriction
  -> left projected scan = full scan on left restriction
  -> reciprocal column estimate
  -> static right-source forcing accumulation
  -> finite-step geometric residual

#4266 physical C5 specialization
  -> card Link > 0
  -> exact physical left column sum
     (card Link - 1) * offFiberInfluence(beta)
  -> physical tagged right-source residual
  -> actual finite-step boundary-response residual

M. VOLUME-UNIFORM LEFT-LEFT CONTROL                            [OPEN NOW]

replace or sharpen the current all-to-all off-fiber majorant
  -> prove actual support / locality / geometry-sensitive coefficient
  -> recompute physical left column sum
  -> obtain a scale-independent contraction criterion if possible

N. ACTUAL CONTINUOUS RESPONSE CERTIFICATE                      [OPEN NEXT]

uniform physical residual + concrete discrepancy/sourceBound witnesses
  -> instantiate FiniteKernelStationaryResponseFamilyCertificate
  -> reuse existing source-resolvent / sweep algebra

O. PHYSICAL POINCARE / COERCIVITY BRIDGE                       [OPEN DOWNSTREAM]

physical response control
  -> relevant block coercivity
  -> six-right + six-left block inequalities
  -> quantitative twelve-spatial coefficient

P. UNIFORM FINITE-VOLUME TRANSFER GAP                          [OPEN DOWNSTREAM]

scale-independent kappa_* > 0
  -> physical transfer-gap lower bound

Q. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                    [OPEN DOWNSTREAM]

uniform finite-volume gap
  -> limiting physical carrier
  -> OS/Wightman spectral lower bound
  -> sufficiently rich same-root 4D Yang--Mills field/state

R. CLAY-LEVEL EXISTENCE + MASS GAP                             [OPEN]
```

---

# Phase 0 — Authority and proof discipline

**Status: Integrated and permanent.**

For theorem-bearing work:

```text
fresh-fetch authoritative branch
-> lock exact canonical SHA
-> inspect exact existing theorem interfaces
-> make the smallest coherent theorem unit
-> RED / failed CI when appropriate
-> inspect the actual Lean failure
-> minimal GREEN patch
-> require terminal completed/success receipt
-> merge with expected_head_sha
-> fresh-fetch canonical branch again.
```

Queued or in-progress CI is not success. New `sorry`, `admit`, axioms, assumption weakening, or semantic broadening are not acceptable substitutes for proof.

Permanent distinctions:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
right-boundary exact cancellation != arbitrary left-left cancellation
one-way carrier zero != a physical zero theorem outside carrier scope
Sum.inl link != Sum.inr link
full tagged random scan != physical restricted random scan
geometric residual formula != geometric decay without rate < 1
finite-step transport != volume-uniform contraction
state-space-independent certificate interface != existence of physical witnesses
stationary response bound != physical coercivity theorem
finite-volume contraction != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion.
```

---

# Phase 1 — Finite Wilson root and OS infrastructure

**Status: Integrated.**

The finite theorem root contains the periodic-even compact `SU(N)` Wilson Gibbs construction, lattice geometry, normalized Haar reference measure, Wilson action, reflection positivity, gauge-covariant structures, spatial-slice carriers, one-slab transfer operators, and positive ground-state architecture.

The route from spatial conditional estimates to a finite-volume physical transfer gap is formalized as routing. What remains downstream is a model-derived quantitative coefficient with the required volume/scale behavior.

---

# Phase 2 — Same-root scalar continuum OS lane

**Status: Integrated as a scalar observable lane.**

The repository constructs a continuum scalar law from finite Wilson readouts, establishes continuum reflection positivity, forms an OS Hilbert carrier, and obtains a real strongly continuous contraction semigroup with self-adjoint Hamiltonian and vacuum structure.

Boundary: this is a same-root scalar continuum lane, not yet the complete four-dimensional Yang--Mills gauge field/state required by the Clay problem.

---

# Phase 3 — Right-boundary C5 normalized locality

**Status: Integrated.**

For the literal C5 reference one-link law, changing a represented right-boundary source distinct from the resampled fiber changes the unnormalized density only by a positive scalar independent of the fiber integration variable. The same scalar multiplies the partition function and cancels after normalization.

Consequently:

```text
source != fiber
-> normalized fiber law equality
-> conditional-kernel equality
-> heat-bath-kernel equality
-> exact zero represented real-test influence.
```

At `source = fiber`, the surviving coefficient is

```text
q(beta)
  = 2 * (exp(16*beta)-1)/(exp(16*beta)+1).
```

The complete represented right-source row is one-point supported, so

```text
rowSum = q(beta),
```

and `0 <= beta < log 3 / 16` implies `q(beta) < 1` with no volume factor.

This right-boundary result must not be reused as a left-left physical cancellation theorem.

---

# Phase 4 — One-way tagged carrier and generic response algebra

**Status: Integrated.**

The proved right-boundary direction is represented on

```text
Sum Link Link
```

with physical left targets in `Sum.inl` and represented right sources in `Sum.inr`.

Only the `Sum.inl <- Sum.inr` block carries the proved cross-boundary coefficient. Other zero blocks are structural carrier choices, not physical assertions about reverse or left-left influence.

The generic finite-kernel layer provides updated variation, random-scan iteration, partial-source sums, reciprocal contraction algebra, source resolvents, and sweep-scaled residual identities.

The state-space-independent certificate introduced before the current physical finite-step program remains the downstream interface. It is not itself a proof that the actual continuous C5 witnesses exist.

---

# Phase 5 — Actual one-link physical variation realization

**Status: Integrated through #4211.**

The physical continuous C5 one-link estimate was lifted from bounded tests to genuine fiber variation and then transported into the represented tagged coefficient:

```text
#4201 actual fiber-variation scaling
#4205 tagged-kernel coefficient transport
#4208 one target-update domination
#4211 full represented right-source row domination.
```

This closes the one-link right-boundary realization but does not control composition across different physical left fibers.

---

# Phase 6 — Same-fiber and distinct-fiber two-step transport

**Status: Integrated through #4237.**

The next problem was genuine physical composition.

PR #4217 proves the narrow same-fiber two-step variation propagation. PR #4220 then introduces an augmented tagged carrier with an explicit left-left off-fiber coefficient rather than reading physical information from the old one-way carrier's structural zeros.

PRs #4223 and #4237 derive the required distinct-fiber transport from the literal continuous C5 conditional law. The raw reference-weight comparison is

```text
exp(32 * beta),
```

which after normalization yields the explicit bounded-test coefficient

```text
offFiberInfluence(beta)
  = 2 * (((exp(32*beta))^2 - 1)
         / ((exp(32*beta))^2 + 1)).
```

The two-step physical theorem is therefore assumption-free in this lane. The coefficient is pointwise volume-independent, but at this stage no claim is made about a volume-uniform sum over all left fibers.

---

# Phase 7 — Deterministic schedule layer

**Status: Integrated by #4242.**

PR #4242 lifts the two-step mechanism to arbitrary finite ordered update lists.

The generic schedule recursion matches repeated `finiteInfluenceKernelUpdatedVariation`, supports append/composition reasoning, and is instantiated with the physical continuous-C5 tagged carrier.

This establishes a mathematically explicit bridge from local continuous heat-bath updates to finite deterministic schedules before any random-scan averaging is introduced.

---

# Phase 8 — Restricted random-scan semantics

**Status: Integrated through #4257.**

A full random scan over `Sum Link Link` would be physically wrong because represented right-source coordinates are parameters, not update targets.

PR #4249 therefore defines the generic restricted-target random scan. It proves exact averaging over singleton deterministic schedules and specializes to the older full scan when the target embedding is `id`.

PR #4252 realizes the actual physical continuous-C5 scan by averaging only over physical left fibers.

PR #4254 proves one-step strong measurability and affine boundary transport under a common left-variation profile.

PR #4257 defines the actual finite-step physical expectation iterate and proves by induction:

```text
strong measurability;
left-fiber variation domination by the restricted tagged iterate;
boundary-parameter transport domination at every finite step.
```

Thus the earlier semantic frontier — physical process versus generic tagged iterate — is closed.

---

# Phase 9 — Generic restricted-target geometric forcing residual

**Status: Integrated by #4260.**

PR #4260 isolates the generic `Sum tau sigma` mechanism needed by the physical chain.

It:

```text
restricts the tagged kernel to left coordinates;
identifies the left projection of the restricted scan with the ordinary scan on that restriction;
inherits reciprocal column contraction on the left carrier;
keeps right coordinates static except for accumulated left forcing;
derives the finite-step right-source geometric forcing residual.
```

The right coordinate is not scanned. Its evolution is forcing accumulation only.

This algebra is generic and does not yet assert that the physical left-restricted coefficient is uniformly contractive.

---

# Phase 10 — Physical C5 geometric residual

**Status: Integrated by #4266.**

PR #4266 specializes the generic residual to the actual physical C5 carrier.

It first proves

```text
0 < card Link
```

without adding assumptions.

It then computes the exact left-restricted column sum:

```text
columnCoefficient(H,beta)
  = (card Link - 1) * offFiberInfluence(beta).
```

The diagonal contribution is exactly zero, and every distinct left target receives the currently proved uniform off-fiber coefficient.

Using this coefficient, #4266 proves the physical tagged right-source residual and composes it with #4257's finite-step boundary transport theorem. The resulting actual physical expectation difference is bounded by the same finite geometric forcing sum.

This closes the **finite-step physical-to-generic bridge**.

Crucial boundary:

```text
geometric forcing residual
```

does not mean

```text
uniform geometric decay.
```

Decay requires a rate below one. The current exact column coefficient still contains `card Link - 1`.

---

# Phase 11 — Sharpen physical left-left support / column control

**Status: OPEN NOW.**

This is the immediate theorem-development frontier after #4266.

The current left-left estimate treats every distinct physical background fiber with the same off-fiber Harnack coefficient. Summing that majorant produces

```text
(card Link - 1) * offFiberInfluence(beta),
```

which does not by itself yield a scale-independent contraction statement.

The next work should inspect the literal C5/Wilson dependence before adding any new abstraction.

## Primary questions

```text
Which background links actually occur in the one-link conditional density?
Can non-neighboring left fibers be shown to have exact zero influence?
Can the coefficient depend on a uniformly bounded local incidence number rather than card Link?
Can a color/block schedule reduce the proved interaction sum to bounded degree?
Is there an additional normalized cancellation hidden by the exp(32 beta) global Harnack majorant?
```

## Preferred proof order

```text
1. expand the exact literal C5 weight dependence on the resampled fiber;
2. isolate each background-link contribution geometrically;
3. prove exact support before estimating magnitudes;
4. assign a coefficient only on the proved support;
5. compute the resulting row/column sum exactly;
6. prove < 1 in a volume-independent coupling region if possible;
7. only after that return to response-certificate packaging.
```

No unproved exponential-decay hypothesis should be inserted merely to remove the cardinality factor.

---

# Phase 12 — Actual continuous response certificate

**Status: OPEN NEXT.**

Once the physical restricted-scan residual has a quantitatively useful uniform coefficient, supply the concrete continuous witnesses required by the existing state-space-independent certificate:

```text
actual discrepancy;
actual sourceBound;
sourceBound nonnegativity;
actual finite-step residual theorem.
```

The intended output remains

```text
FiniteKernelStationaryResponseFamilyCertificate.
```

The certificate interface is already proved; this phase is physical witness construction, not new generic algebra.

---

# Phase 13 — Re-enter source-resolvent and sweep algebra

**Status: Generic algebra integrated; physical instantiation open.**

With the actual continuous certificate available, reuse the existing machinery rather than reproving it:

```text
continuous certificate
-> source partial response
-> source-summed resolvent
-> normalized source average
-> reciprocal random-scan terminal residual
-> sweep-scaled response bound.
```

Any sweep statement must use the correct physical restricted target count and the newly proved physical contraction coefficient, not the older full tagged-cardinality semantics.

---

# Phase 14 — Physical Poincare/coercivity bridge

**Status: Open downstream.**

The response result must then be connected to the genuine physical spatial conditional-expectation family already present in the finite Wilson/ground-state lane.

The target direction remains

```text
physical response / variation control
  -> same-color or relevant block coercivity
  -> six-right + six-left block inequalities
  -> quantitative twelve-spatial Poincare coefficient kappa.
```

No present C5 finite-step theorem is itself this coercivity theorem.

---

# Phase 15 — Uniform finite-volume transfer gap

**Status: Open downstream; routing integrated.**

The existing routing shows that a scale-independent positive twelve-spatial coefficient would imply a quantitative physical transfer-gap lower bound.

A positive coefficient at each fixed volume is insufficient if it degenerates along the volume/scaling sequence.

---

# Phase 16 — Thermodynamic and continuum physical propagation

**Status: Open downstream.**

A finite-volume transfer gap must still be transported through the thermodynamic/scaling limit into a limiting physical carrier. This requires explicit convergence, tightness, compatibility, and spectral-stability theorems strong enough to preserve the relevant lower bound.

The already-integrated scalar continuum OS lane is not a substitute for the complete physical four-dimensional gauge-field/state construction.

---

# Phase 17 — Clay-level endpoint

**Status: Open.**

The final endpoint still requires a sufficiently rich four-dimensional Yang--Mills field/state satisfying the relevant mathematical-physics requirements together with a strictly positive spectral gap above the vacuum.

The current C5 program is a concrete local-to-finite-step comparison route toward that endpoint. It must not be described as a completed Clay proof before the remaining uniform left-left control, physical response/certificate, coercivity, finite-volume uniformity, and continuum obligations are discharged.

---

# Immediate next theorem unit

Starting from fresh canonical theorem-carrier SHA

```text
2ebe3ee4a69a662a2010d5e2a41ba1b1953289bc,
```

the next coherent unit should be:

```text
1. inspect the exact dependence graph of the literal C5 one-link conditional weight;
2. classify physical left background fibers into actual-support and no-dependence classes;
3. prove exact zero outside the support whenever the formula permits it;
4. derive the sharp supported left-left influence coefficient;
5. compute the supported left-restricted column sum;
6. test whether the resulting coefficient is bounded below 1 uniformly in H for a fixed coupling range;
7. if yes, specialize #4260/#4266 to that uniform coefficient;
8. then instantiate the actual continuous response certificate.
```

The intended direction is therefore

```text
finite-step physical bridge                       [CLOSED]
-> sharpen physical left-left locality            [OPEN NOW]
-> volume-uniform restricted-scan contraction     [OPEN]
-> actual continuous response certificate         [OPEN]
-> source-resolvent / sweep response              [GENERIC ALGEBRA READY]
-> physical Poincare / coercivity                  [OPEN]
-> uniform finite-volume gap                      [OPEN]
-> thermodynamic / continuum physical gap         [OPEN]
-> Clay-level Yang--Mills existence + mass gap    [OPEN].
```
