# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, conditional expectations, quantitative mixing, coercivity, and the mass-gap problem.

The repository deliberately separates exact finite-volume theorems, continuous-state realizations, generic comparison algebra, physical finite-step transport, thermodynamic/continuum passages, and the final Clay-level target.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current C5 continuous `SU(N)` program has advanced substantially beyond one-link control. The actual physical continuous heat-bath chain is now represented by a **restricted random scan** that updates only physical `Sum.inl` fibers; represented `Sum.inr` boundary-source coordinates are never scanned. Strong measurability, finite-step variation domination, boundary-parameter transport, the generic restricted-target geometric forcing residual, and its physical C5 specialization are all formalized through PR #4266.
>
> The immediate obstruction is now quantitative rather than semantic: the physical left-left off-fiber propagation produces the exact restricted-column coefficient
>
> ```text
> (card Link - 1) * offFiberInfluence(beta).
> ```
>
> Therefore the current finite-step residual theorem is rigorous, but it is **not yet a volume-uniform contraction theorem**. A sharper physical locality/support estimate, a geometry-sensitive coefficient, or another rigorously justified decomposition is required before this lane can feed a scale-independent coercivity/gap estimate.

---

## Repository authority — 2026-09-16 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem-carrier branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Current authoritative exact HEAD:
  2ebe3ee4a69a662a2010d5e2a41ba1b1953289bc

Current tree:
  b87194cad77d5136d02797ca2a9a88689d9944d2

Latest theorem-bearing merge:
  PR #4266
  Specialize restricted-target geometric residual to physical C5

Exact GREEN proof head:
  7c9d0662a30fd8d0006553aa7215014e6f577093

Validation receipt:
  PR Lean Fast Check #13971
  workflow run 35063053481
  completed / success

Public landing branch:
  main
```

The authority order is fixed:

```text
1. exact canonical GitHub SHA on the theorem-carrier branch
2. formal Lean artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

`main` is a public landing surface, not theorem authority when histories differ. Always fresh-fetch the theorem-carrier branch before theorem work.

---

# Current proof spine

```text
FINITE WILSON / OS ROOT
  periodic-even compact SU(N) Wilson model
  -> reflection positivity / OS carriers
  -> one-slab transfer and ground-state structure
  -> spatial conditional-expectation / coercivity routing
                                                        [INTEGRATED]

SAME-ROOT SCALAR CONTINUUM OS LANE
  finite Wilson scalar readout
  -> continuum scalar law
  -> reflection positivity
  -> OS Hilbert carrier / C0 semigroup / Hamiltonian
                                                        [INTEGRATED]

C5 CONTINUOUS ONE-LINK LAW
  literal normalized continuous SU(N) fiber law
  -> measurable heat-bath sampling and reinsertion
  -> exact right-boundary distinct-source cancellation
  -> sharp surviving diagonal right-source coefficient
                                                        [INTEGRATED]

ONE-WAY RIGHT-BOUNDARY CARRIER
  Sum.inl target <- Sum.inr source
  exact represented support
  row / right-source-column coefficient q(beta)
  beta < log 3 / 16 -> q(beta) < 1
                                                        [INTEGRATED]

ACTUAL PHYSICAL LEFT-LEFT TRANSPORT
  same-fiber two-step propagation
  -> distinct-fiber Harnack / conditional-law comparison
  -> explicit off-fiber coefficient
  -> assumption-free two-step transport
                                                        [INTEGRATED]

DETERMINISTIC SCHEDULES
  generic finite update lists
  -> exact tagged schedule recursion
  -> continuous C5 physical schedule transport
                                                        [INTEGRATED]

RESTRICTED RANDOM SCAN
  generic restricted-target scan
  -> physical targets exactly Sum.inl fiber
  -> Sum.inr boundary-source coordinates remain static
  -> one-step physical scan
  -> finite-step measurable expectation iterate
  -> left-variation domination
  -> boundary-parameter transport domination
                                                        [INTEGRATED]

GEOMETRIC FORCING RESIDUAL
  generic Sum tau sigma left restriction
  -> left-only reciprocal random-scan estimate
  -> static right-source forcing accumulation
  -> finite-step geometric residual
  -> physical C5 specialization
                                                        [INTEGRATED THROUGH #4266]

QUANTITATIVE FRONTIER
  physical left-restricted column sum
    = (card Link - 1) * offFiberInfluence(beta)
  -> rigorous finite-step residual exists
  -> volume-uniform contraction NOT YET proved
                                                        [OPEN NOW]

DOWNSTREAM
  sharpen physical left-left locality / column control
  -> actual continuous response certificate
  -> source resolvent / sweep algebra
  -> physical Poincare / coercivity
  -> uniform finite-volume transfer gap
  -> thermodynamic/scaling-limit physical carrier
  -> sufficiently rich 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
                                                        [OPEN]
```

---

# 1. Two distinct influence structures must not be conflated

The current C5 lane contains two mathematically different influence mechanisms.

## 1.1 Right-boundary source -> left target

For the literal C5 reference one-link law, changing a represented right-boundary source at a coordinate distinct from the resampled fiber multiplies the unnormalized density by a positive scalar independent of the integration variable. The same scalar multiplies the partition function and cancels after normalization.

Hence

```text
source != fiber
```

implies exact equality of the normalized fiber laws, conditional kernels, and heat-bath kernels. The represented real-test influence is exactly zero.

Only

```text
source = fiber
```

survives, with

```text
q(beta)
  = 2 * (exp(16*beta) - 1) / (exp(16*beta) + 1).
```

Thus the represented right-source row is one-point supported and

```text
rowSum = q(beta).
```

For `0 <= beta < log 3 / 16`, one has `0 <= q(beta) < 1` with no spatial-volume factor.

## 1.2 Left background fiber -> different left resampling fiber

Finite-step physical composition introduces a different question: after one physical heat-bath update, how much can changing another **left** background fiber alter the next one-link law?

This is not covered by the structurally-zero left-left block of the old one-way carrier. PRs #4220--#4237 construct and discharge the missing physical theorem instead.

The literal comparison currently gives the explicit off-fiber coefficient

```text
offFiberInfluence(beta)
  = 2 * (((exp(32*beta))^2 - 1)
         / ((exp(32*beta))^2 + 1)).
```

The coefficient is volume-independent pointwise, but when the physical restricted scan sums over all left targets, PR #4266 proves the exact column identity

```text
columnSum
  = (card Link - 1) * offFiberInfluence(beta).
```

This explicit cardinality factor is the present quantitative bottleneck.

---

# 2. Why the scan is restricted

The physical chain does **not** update all coordinates of

```text
Sum Link Link.
```

Its meanings are:

```text
Sum.inl fiber  = physical left fiber that may be heat-bath updated
Sum.inr source = represented right-boundary source parameter
```

Only `Sum.inl` coordinates are physical scan targets. `Sum.inr` coordinates are static bookkeeping coordinates that accumulate forcing from the evolving left variation profile.

This distinction is now built into the formalization rather than left as an interpretation:

```text
#4249  generic restricted-target random scan
#4252  actual physical continuous C5 restricted random scan
#4254  one-step affine transport / measurability induction nucleus
#4257  finite-step physical expectation iterate and transport domination
#4260  generic restricted-target geometric forcing residual
#4266  physical C5 specialization
```

Accordingly, the repository no longer needs to identify the physical continuous process with the older full random scan over `Sum Link Link`.

---

# 3. Finite-step bridge now proved

The earlier documentation frontier was the passage from one-link continuous variation estimates to a genuine multi-step physical process. That bridge is now integrated.

The formal chain is:

```text
one-link continuous C5 variation estimate
  -> physical same-fiber two-step propagation
  -> physical distinct-fiber transport
  -> arbitrary finite deterministic schedules
  -> restricted random-scan one-step transport
  -> finite-step physical expectation iterate
  -> tagged restricted-target variation iterate domination
  -> right-source geometric forcing residual.
```

The final #4266 theorem bounds the actual finite-step boundary-parameter response of the physical continuous C5 restricted random-scan expectation by the same geometric forcing residual obtained from the tagged kernel.

This is a genuine physical-to-generic bridge. It is not merely an interface declaration.

---

# 4. What #4266 proves — and what it does not

PR #4266 proves three key facts.

First, the physical spatial-link carrier is nonempty, so the generic reciprocal random-scan denominator is legitimate without adding a new geometric assumption.

Second, the left-restricted tagged-kernel column sum is computed exactly:

```text
(card Link - 1) * offFiberInfluence(beta).
```

Third, the actual finite-step physical boundary response is bounded by a residual of the form

```text
(card Link)^(-1)
* sourceCoefficient
* initialVariationBound
* sum_{j < n} rate(columnCoefficient)^j.
```

The word **geometric** here describes the proved algebraic form. It does not by itself imply decay. Decay requires a contraction hypothesis strong enough to make the relevant reciprocal random-scan rate strictly below one.

At present the theorem does not remove the `card Link - 1` factor from the physical left-left column coefficient. Therefore #4266 is not yet a uniform mixing, uniform Poincare, or uniform mass-gap theorem.

---

# 5. Current theorem-development frontier

The next mathematical unit is to improve or reorganize the physical left-left propagation so that the finite-step theorem becomes useful uniformly in volume.

Admissible routes include proving, from the literal C5/Wilson structure rather than assumption, one of the following:

```text
finite-range support of left-left influence;
geometry-sensitive neighbor coefficients with uniformly bounded row/column sum;
additional exact cancellation;
a color/block schedule whose proved interaction degree is volume independent;
or another physical decomposition that avoids all-to-all cardinality growth.
```

An unproved `C * exp(-m*d)` assumption must not simply be inserted to close this gap.

Once a scale-independent physical contraction coefficient is available, the intended route is

```text
uniform restricted-scan contraction
  -> package actual continuous discrepancy/sourceBound witnesses
  -> FiniteKernelStationaryResponseFamilyCertificate
  -> existing source-resolvent / sweep machinery
  -> physical Poincare / coercivity
  -> uniform finite-volume transfer gap.
```

---

# 6. Permanent semantic boundaries

The following distinctions remain part of the proof discipline:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
right-boundary exact cancellation != arbitrary left-left cancellation
one-way tagged zero block != reverse or left-left physical influence zero
Sum.inl link != Sum.inr link
full tagged random scan != physical restricted random scan
geometric residual formula != geometric decay without rate < 1
finite-step physical transport != volume-uniform contraction
state-space-independent certificate interface != existence of physical witnesses
stationary response control != physical coercivity theorem
finite-volume gap != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion
```

---

# 7. Near-term target

Starting from exact canonical HEAD

```text
2ebe3ee4a69a662a2010d5e2a41ba1b1953289bc
```

the preferred next sequence is:

```text
1. inspect the literal C5 left-left dependence geometrically;
2. determine which background fibers can actually affect a resampled fiber;
3. replace the all-to-all offFiberInfluence majorant by the sharpest proved support/coefficient structure;
4. recompute the restricted left column sum;
5. prove a volume-uniform contraction criterion if the model permits it;
6. only then instantiate the continuous response certificate and re-enter the existing resolvent/coercivity route.
```

The repository therefore stands at a clear boundary: the **multi-step physical bridge is closed**, while the **volume-uniform quantitative control of physical left-left propagation remains open**.
