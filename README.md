# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, conditional expectations, quantitative mixing, coercivity, and the mass-gap problem.

The repository deliberately separates exact finite-volume theorems, conditional comparison interfaces, continuous-state realizations, thermodynamic/continuum passages, and the final Clay-level target.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current theorem frontier is much narrower than the earlier remote-influence problem. The C5 continuous `SU(N)` reference one-link law now has an exact off-diagonal cancellation theorem, an explicit diagonal influence coefficient, a one-way tagged influence carrier, generic reciprocal random-scan/resolvent algebra, a state-space-independent response-certificate interface, and an actual continuous one-link **fiber-variation** realization through a full represented right-source row.
>
> What is still missing is the rigorous multi-step bridge from those physical continuous one-link estimates to the generic tagged finite-step variation iterate and hence to the continuous finite-step kernel residual required by the certificate. That bridge must be proved; the generic tagged random-scan process is not identified with a physical continuous random-scan chain by definition.

---

## Repository authority — 2026-09-15 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem-carrier branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest theorem-bearing merge before this documentation refresh:
  a05876f44f1bf387ad070889de6487bd37b2121b

Tree:
  2751d346ef5149f1e31848eeb5089c8d1ceb9061

Merge:
  PR #4211
  Lift continuous C5 heat-bath variation to row operator

Exact final GREEN proof head:
  3e570acaacd62d1ce50c1558587d7b6d53917a07

Validation receipt:
  PR Lean Fast Check #13919
  workflow run 34961303873
  workflow / job / changed-Lean step: completed / success

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

`main` is a public landing surface, not theorem authority when histories differ. A docs-only merge can advance a branch pointer without changing the latest theorem-bearing result, so always fresh-fetch the authoritative theorem-carrier branch before starting theorem work.

---

# Current proof spine

```text
FINITE WILSON / OS ROOT
  periodic-even compact SU(N) Wilson model
  -> reflection positivity / OS carriers
  -> one-slab transfer and ground-state structure
  -> spatial conditional-expectation / coercivity routing
                                                        [INTEGRATED]

C5 CONTINUOUS ONE-LINK LAW
  literal normalized continuous SU(N) fiber law
  -> measurable heat-bath sampling and reinsertion
  -> source-local factorization
  -> exact distinct-source normalized invariance
                                                        [INTEGRATED]

C5 CROSS-BOUNDARY INFLUENCE
  source != fiber
    -> normalized fiber laws equal
    -> conditional kernels equal
    -> heat-bath kernels equal
    -> real-test influence = 0

  source = fiber
    -> sharp normalized Harnack comparison
    -> coefficient
       q(beta) = 2 * (exp(16 beta)-1)/(exp(16 beta)+1)
                                                        [INTEGRATED]

ONE-WAY TAGGED CARRIER
  index ι_H = Sum Link Link
  populated block only:
    Sum.inl target <- Sum.inr source
  row sum = q(beta)
  right-source column sum = q(beta)
  other blocks = carrier-scope zeros only
                                                        [INTEGRATED]

SMALL-COUPLING / GENERIC KERNEL ALGEBRA
  beta < log 3 / 16
    -> 0 <= q(beta) < 1

  r_{H,beta}
    = 1 - (1-q(beta))/|ι_H|

  r_{H,beta}^{|ι_H| * sweeps}
    <= exp(-(1-q(beta))*sweeps)
                                                        [INTEGRATED]

STATE-SPACE-INDEPENDENT RESPONSE INTERFACE
  FiniteKernelStationaryResponseFamilyCertificate
  -> discrepancy
  -> sourceBound
  -> nonnegative variation profile
  -> finite-step kernel residual
  -> source-summed resolvent / geometric residual
                                                        [INTEGRATED INTERFACE]

ACTUAL CONTINUOUS SU(N) REALIZATION
  bounded-test influence
  -> fiber-variation-scaled influence                  [#4201]
  -> represented tagged kernel coefficient            [#4205]
  -> one generic tagged target-update domination       [#4208]
  -> full represented right-source row
     <= physical cross-boundary influence operator     [#4211]
                                                        [INTEGRATED]

NEXT BRIDGE
  actual continuous one-link update sequence
  -> rigorous multi-step variation domination
  -> finite-step continuous kernel residual
  -> actual continuous response certificate
                                                        [OPEN NOW]

DOWNSTREAM
  actual continuous certificate
  -> already-proved source resolvent / sweep residual
  -> physical block Poincare / coercivity bridge
  -> uniform finite-volume transfer gap
  -> thermodynamic/scaling-limit physical carrier
  -> sufficiently rich 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
                                                        [OPEN]
```

---

# 1. Exact C5 support and the scalar coefficient

For the literal C5 continuous reference fiber law, changing a right-boundary source value at a coordinate distinct from the resampled fiber changes the unnormalized weight only by a positive scalar independent of the fiber integration variable. The same scalar multiplies the partition function, so it cancels after normalization.

Thus, for

```text
source != fiber,
```

the normalized fiber probability measures are literally equal. This equality propagates through the conditional kernel and the full heat-bath sampling/reinsertion kernel. The corresponding real-test source influence is exactly zero.

The only surviving represented C5 cross-boundary source is

```text
source = fiber.
```

Its coefficient is

```text
q(beta)
  = 2 * (((exp (8*beta))^2 - 1) / ((exp (8*beta))^2 + 1))
  = 2 * (exp (16*beta) - 1) / (exp (16*beta) + 1).
```

Therefore the complete represented source row has one-point support and

```text
rowSum = q(beta),
```

with no spatial-volume or color-class cardinality factor. For nonnegative coupling,

```text
beta < log 3 / 16
```

implies

```text
0 <= q(beta) < 1.
```

No spatial hypothesis of the form `C * exp(-m*d)` is used in this C5 contraction route.

---

# 2. One-way tagged carrier: exact mathematics, restricted semantics

The proved direction is packaged on

```text
ι_H = Sum Link Link.
```

with

```text
Sum.inl = left target copy
Sum.inr = right source copy.
```

Only

```text
Sum.inl target <- Sum.inr source
```

contains the proved C5 cross-boundary coefficient. The remaining blocks are zero by definition of the **one-way carrier**.

This must not be overinterpreted. In particular,

```text
K.influence (Sum.inr target) (Sum.inl source) = 0
```

inside the carrier is not a theorem that reverse physical influence vanishes. Likewise `Sum.inl link` and `Sum.inr link` are distinct tagged coordinates and must not be collapsed.

The tagged carrier has the exact row/column structure required by the generic finite-kernel machinery. In the small-coupling region its reciprocal random-scan rate is

```text
r_{H,beta} = 1 - (1-q(beta))/|ι_H|.
```

The one-coordinate rate is volume dependent. The volume-independent statement appears only after measuring time in full tagged sweeps:

```text
r_{H,beta}^{|ι_H| * sweeps}
  <= exp(-(1-q(beta))*sweeps).
```

---

# 3. Generic response algebra is already factored away from the local state space

The downstream response machinery no longer requires the local state space itself to be finite.

`FiniteKernelStationaryResponseFamilyCertificate` retains only the information needed by the kernel algebra:

```text
discrepancy
sourceBound
sourceBound_nonneg
variation profile
variation_nonneg
finite-step kernel residual inequality
```

PR #4192 factors the source-summed resolvent/geometric-residual argument through this certificate. PR #4198 adds a continuous-state packaging entry point that constructs the certificate once the actual discrepancy, source bound, and finite-step residual witnesses have been proved.

That is an interface, not an existence theorem. No finite `G` should be reintroduced merely to satisfy it.

The finite positive-weight lane remains useful as one realization of the interface. In that lane, the normalized source-average term has also been sharpened, including the local-tilt source average and pointwise stationary source-bound route from PRs #4187 and #4190. Those results do not by themselves construct the actual continuous physical certificate.

---

# 4. What #4201, #4205, #4208, and #4211 add

The continuous-state realization now reaches the profile-operator level.

### PR #4201 — fiber variation, not only `|F| <= 1`

For the actual continuous `SU(N)` one-link C5 heat-bath kernel, if the oscillation of an observable along the resampled fiber is bounded by `magnitude`, then changing the represented right-boundary source value changes the heat-bath expectation by at most

```text
CrossBoundaryBoundedTestMajorant beta fiber source * magnitude.
```

This uses no finite local state space.

### PR #4205 — transport into the tagged kernel coefficient

The same bound is rewritten exactly as the represented tagged kernel entry

```text
K.influence (Sum.inl fiber) (Sum.inr source) * magnitude.
```

This is only a transport theorem; it adds no reverse physical semantics.

### PR #4208 — one target-update recurrence nucleus

A physical left-fiber variation profile is lifted to the tagged carrier by

```text
Sum.inl fiber  -> variation fiber
Sum.inr source -> 0.
```

The right-copy zero is bookkeeping for a left-fiber observable, not a reverse-influence theorem. The actual continuous one-source heat-bath influence is then bounded by one generic

```text
finiteInfluenceKernelUpdatedVariation
```

step at the represented `(Sum.inl fiber, Sum.inr source)` pair.

### PR #4211 — full represented source row

The one-source theorem is summed over all represented right-boundary sources. The actual continuous one-link source row is bounded by

```text
periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryInfluenceOperator
  H beta variation fiber.
```

The proof unfolds the influence operator, applies the continuous fiber-variation estimate source-by-source, and uses exact diagonal support for the off-diagonal terms.

This is the strongest current physical continuous C5 variation theorem in this lane.

---

# 5. Immediate frontier: finite-step continuous variation propagation

The next missing theorem is **not** another one-step coefficient estimate. It is the descent from the actual continuous update dynamics to the already-existing finite-kernel iteration algebra.

The generic objects

```text
finiteInfluenceKernelUpdatedVariation
finiteInfluenceKernelRandomScanUpdatedVariation
finiteInfluenceKernelRandomScanVariationIterate
finiteInfluenceKernelPartialSource
```

are already implemented and have the needed positivity, monotonicity, scaling, and resolvent infrastructure.

What is not yet proved is that an actual continuous sequence of C5 heat-bath updates is dominated, step after step, by the relevant generic tagged variation update/iterate.

A crucial obstruction must remain explicit:

```text
generic tagged random scan over Sum Link Link
  != by definition
actual physical continuous random scan/update sequence.
```

The next proof must therefore either:

1. construct the physical update sequence and prove compatibility/domination by the tagged operator; or
2. formulate a narrower continuous update composition whose variation recurrence is exactly sufficient for the finite-step residual, without claiming an unjustified process identity.

Only after this bridge is proved should the project claim the continuous finite-step residual required by #4198.

---

# 6. Target finite-step residual

The intended continuous witness has the same state-space-independent shape already consumed downstream:

```text
discrepancy source
  <= finiteInfluenceKernelPartialSource
       K sourceEnvelope variation n
     + 2 * finiteProductVariationTotal
       (finiteInfluenceKernelRandomScanVariationIterate
         K variation n).
```

For the singleton family used by the C5 source-summed theorem, `variation` is the corresponding singleton tagged variation profile.

Once this inequality and the genuine continuous `sourceBound` witnesses are obtained, #4198 can package them directly into `FiniteKernelStationaryResponseFamilyCertificate`, after which #4192 and the existing C5 resolvent/sweep algebra apply without referring to a finite local state space.

---

# 7. Permanent claim boundaries

The present theorem tree does **not** license any of the following identifications or conclusions:

- C5 raw one-slab law = full-4D Wilson `singleLinkConditionalMeasure`;
- distinct-source C5 invariance = arbitrary full-4D remote influence zero;
- one-way tagged zero block = reverse physical influence zero;
- `Sum.inl link` = `Sum.inr link`;
- generic tagged random scan = actual continuous physical random scan;
- one-coordinate random-scan rate = volume-uniform contraction rate;
- finite positive-weight comparison = continuous `SU(N)` comparison;
- `FiniteKernelStationaryResponseFamilyCertificate` = automatic existence of physical witnesses;
- PR #4198 = construction of the actual physical continuous certificate;
- stationary comparison = physical Poincare/coercivity theorem;
- finite-volume contraction = thermodynamic/continuum mass gap;
- same-root scalar continuum lane = complete 4D Yang--Mills field/state;
- any unproved spatial decay `C * exp(-m*d)`;
- completion of the Clay Yang--Mills mass-gap problem.

---

# 8. Verification discipline

The active theorem-development workflow is intentionally strict:

```text
fresh-fetch exact canonical branch
-> branch from exact SHA
-> RED theorem / Draft PR
-> terminal failed Lean receipt
-> inspect actual root cause
-> minimal GREEN patch
-> terminal successful workflow/job/Lean-step receipt
-> record exact GREEN SHA and CI run
-> Ready for review
-> merge with expected_head_sha
-> fresh re-observe canonical branch and tree
```

Queued, pending, or in-progress CI is never treated as success. New `sorry`, `admit`, axioms, assumption weakening, and semantic broadening of one-way carrier zeros are not acceptable substitutes for proof.

For the detailed theorem-development order, see [`ROADMAP.md`](ROADMAP.md).
