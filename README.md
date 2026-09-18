# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, conditional expectations, quantitative mixing, coercivity, and the mass-gap problem.

The repository is deliberately layered. Exact finite-volume results, continuous-state realizations, local C5 geometry, fixed-right response identities, physical restricted-scan transport, coercivity routing, continuum constructions, and the eventual Clay-level target are kept logically separate.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current continuous `SU(N)` C5 lane has progressed substantially beyond the earlier dense all-links Harnack majorant. Remote target-ratio responses are now aggregated exactly, the first nontrivial restricted-scan transport is computed, the two-step represented-source transport is bounded uniformly in volume, and the formerly opaque two-step stationary terminal response has been reduced to an explicit propagated physical-left variation mass.
>
> The present quantitative obstruction is therefore sharper: prove that the aggregate propagated left mass and the corresponding fixed-right response family admit a **volume-uniform sparse/local closure**, without falling back to the dense `(card Link - 1) * offFiberInfluence` majorant and without assuming the global contraction one is trying to prove.

---

## Repository authority — documentation baseline 2026-09-18 JST

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The exact merged theorem-carrier commit used to write this documentation is

```text
9fbe314d4245c19fffa5762f8de683d3ab7d35fe
```

with tree

```text
8bb7d9e4928b132256dae655fea73e0620986397
```

This is the merge of PR #4421:

```text
Descend two-step terminal response to aggregate left variation mass
```

Its exact GREEN proof head was

```text
4b45573fc01111d5a18894e7332692a66d95c119
```

The pull-request validation completed successfully before merge. The merge-push validation on the authoritative theorem-carrier branch also completed successfully and saved the trusted Lake build cache.

This README/ROADMAP refresh is docs-only. Once merged, the branch pointer will advance even though the theorem-bearing mathematical baseline remains the latest Lean theorem merge until another theorem PR lands. Therefore **always fresh-fetch the theorem-carrier branch before theorem work**. A SHA printed in documentation is a historical baseline, not live authority.

Authority order:

```text
1. exact current GitHub SHA on the authoritative theorem-carrier branch
2. formal Lean artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

`main` is a public landing surface, not theorem authority when histories differ.

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

CONTINUOUS C5 ONE-LINK LAW
  normalized continuous SU(N) fiber law
  -> measurable heat-bath reinsertion
  -> exact right-boundary off-target cancellation
  -> sharp surviving represented-source coefficient
                                                        [INTEGRATED]

LOCAL C5 GEOMETRY
  target-local factor locality
  -> intrinsic spatial plaquette-neighbor degree <= 18
  -> C5 exceptional set <= 20
  -> remote raw Wilson four-point distortion cancels
                                                        [INTEGRATED]

FIXED-RIGHT GROUND-STATE RESPONSE
  kernel-section probability law
  -> right update as normalized tilt
  -> two-source crossing response
  -> remote target-ratio response
                                                        [INTEGRATED]

PHYSICAL RESTRICTED-SCAN TRANSPORT
  deterministic schedules
  -> restricted random scan over physical Sum.inl fibers
  -> measurable finite-step expectation iterate
  -> tagged variation propagation
                                                        [INTEGRATED]

REMOTE TARGET-RATIO AGGREGATION
  remote singleton target variations
  -> exact aggregate profile
  -> all-coordinate finite superposition
  -> one-step right-source delay = 0
  -> exact one-step left carrier
  -> exact first nonzero two-step right-source response
                                                        [INTEGRATED]

TWO-STEP REMOTE CLOSURE
  aggregate two-step right-source transport
  -> volume-independent upper bound
  -> continuous-state finite-coordinate telescoping
  -> terminal remote column <= 2 * aggregate left total mass
                                                        [INTEGRATED THROUGH #4421]

QUANTITATIVE FRONTIER
  control the aggregate propagated physical-left mass
  and convert the fixed-right response family into a genuine
  volume-uniform physical remote influence column rho
                                                        [OPEN NOW]

VOLUME-INDEPENDENT C5 GATE
  exceptional contribution <= 20 * eta
  remote residual column <= rho
  20 * eta + rho < 1
  -> strict physical column contraction
                                                        [INTEGRATED INTERFACE]

DOWNSTREAM
  concrete response certificate
  -> source resolvent / sweep algebra
  -> physical Poincare / coercivity
  -> uniform finite-volume transfer gap
  -> thermodynamic/scaling-limit physical carrier
  -> sufficiently rich 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
                                                        [OPEN]
```

---

# 1. What is already volume-independent

## 1.1 Exact represented right-source locality

For the literal continuous C5 one-link law, changing a represented right-boundary source distinct from the resampled physical fiber multiplies the unnormalized one-link density by a scalar independent of the integration variable. Normalization cancels that scalar exactly.

Only the matching represented source survives, with coefficient

```text
q(beta)
  = 2 * (exp(16*beta) - 1) / (exp(16*beta) + 1).
```

Hence

```text
0 <= beta < log 3 / 16
```

implies

```text
q(beta) < 1
```

without a spatial-volume factor.

This is a one-way represented-source statement. It is **not** a theorem that arbitrary physical left-left influence vanishes.

## 1.2 Bounded local Wilson geometry

For a spatial link, the number of distinct intrinsic spatial links sharing a spatial Wilson plaquette is at most

```text
18.
```

After adjoining the resampled fiber and distinguished right target, the relevant C5 exceptional set has cardinality at most

```text
20
```

uniformly in periodic volume.

This is a theorem about the bare/local Wilson interaction geometry. It does not by itself prove decay of the globally synthesized ground state.

## 1.3 The dense off-fiber majorant remains only a fallback bound

The older coefficient

```text
(card Link - 1) * offFiberInfluence(beta)
```

is still a valid coarse majorant obtained by assigning one common distinct-fiber Harnack estimate to every other physical link.

It is no longer the preferred description of the geometry. Using it too early reintroduces precisely the volume factor the current remote-response program is designed to avoid.

---

# 2. Remote defects are exact fixed-right probability responses

Outside the C5 exceptional set, the target-local Wilson factor and the raw one-slab four-point Wilson distortion cancel exactly. The remaining defect is carried by the continuous physical ground state.

The relevant fixed-right weight is

```text
w_C(A) = Omega(A) * K(A,C),
```

with positive finite mass

```text
Z_C = integral w_C dmu > 0,
```

which defines the normalized probability law

```text
nu_C = w_C dmu / Z_C.
```

The remote weighted defect is converted exactly into a covariance under `nu_C`, then into a fixed-right source response.

The response chain through #4355 is:

```text
one-link vacuum response
-> fixed-right kernel-section expectation
-> right update as normalized local tilt
-> two-source crossing response
-> literal target-local ratio specialization
-> exact remote reference-law / kernel-section identification
-> remote C5 covariance = fixed-right expectation response.
```

These are exact identities. They do not assert decay.

---

# 3. The actual stationary restricted C5 response is formalized

The physical random scan updates only actual left spatial fibers:

```text
Sum.inl fiber  = physical left fiber, eligible for scan updates
Sum.inr source = represented right-boundary source parameter
```

The represented source is never itself a scan target.

For the fixed-right target-ratio observable

```text
F_target(A)
  = localFactor(A,target,g1) / localFactor(A,target,g2),
```

the repository proves positivity, strong measurability, integrability, and the singleton physical variation profile

```text
variation_target(e)
  = exp(16*beta)   if e = target,
    0              otherwise.
```

For a remote target/source pair, the stationary response is bounded by

```text
finite-step represented-source transport
+ terminal difference of the common smoothed observable.
```

The initial variation is supported at exactly one physical target; no volume-wide initial profile is inserted.

---

# 4. Remote aggregation is now exact

The major advance after #4367 is that the remote targets are no longer treated only one at a time.

Let

```text
RemoteAggregateVariation
  = sum_{target in remote C5 set} variation_target.
```

The formalization now proves:

```text
#4399  source-coordinate aggregate identity

#4403  pointwise characterization:
       RemoteAggregateVariation(e)
       = exp(16*beta) on remote target fibers,
         0 otherwise

#4406  exact all-coordinate finite superposition:
       Q^n(RemoteAggregateVariation)(e)
       = sum_remote Q^n(variation_target)(e)

#4409  one-step represented right-source aggregate response = 0.
```

The key structural point is that summation over remote targets can be performed **before** the quantitative estimate. This is necessary for any volume-uniform column bound.

---

# 5. The first nontrivial aggregate transport is explicit

## 5.1 One-step physical-left carrier — #4412

The aggregate one-step left-source coefficient is computed exactly. Its remote-cardinality factor appears only as the normalized ratio

```text
(remote.card : R) * (card Link : R)^-1.
```

Thus the first physical-left carrier does not force a naked volume multiplier.

## 5.2 First nonzero represented-source response — #4415

The aggregate represented right-source response is exactly zero at one scan step and becomes nonzero at two steps.

The two-step exact term has the expected structure

```text
normalized remote fraction
* represented-source coefficient
* off-fiber physical-left coefficient
* exp(16*beta).
```

This proves the actual two-hop route:

```text
remote target variation
-> physical left carrier
-> represented right source.
```

## 5.3 Volume-independent two-step right-source bound — #4418

Rather than bounding the exact remote-cardinality expression directly, the proof embeds the remote set into the complete non-source column and reuses the already-proved nonnegative two-step column estimate.

The result is a two-step represented-source transport bound independent of periodic volume.

This closes the **transport** half of the two-step residual.

---

# 6. The terminal term is no longer opaque

PR #4421 removes the earlier stationary-measure black box at two steps.

It adds a generic continuous-state finite-coordinate telescoping theorem:

```text
if each coordinate update changes f by at most variation(e),
then
|f(A) - f(B)| <= sum_e variation(e).
```

Crucially, the coordinate **value space need not be finite**. This is the form needed for `SU(N)`.

For two arbitrary probability measures on the finite coordinate carrier, the current theorem then gives

```text
|E_mu f - E_nu f|
<= 2 * sum_e variation(e).
```

Applying this to the two-step smoothed target-ratio observable yields

```text
TwoStepTerminalResponseAbs(target,source)
<= 2 *
   sum_{physical e}
     Q^2(variation_target)(Sum.inl e).
```

Summing over remote targets and using exact aggregate superposition gives

```text
TwoStepTerminalRemoteColumn
<= 2 *
   sum_{physical e}
     Q^2(RemoteAggregateVariation)(Sum.inl e).
```

Therefore the two-step stationary remote response has been reduced to two concrete tagged quantities:

```text
A. a volume-independent represented right-source transport term;
B. the total propagated physical-left mass of the aggregate remote profile.
```

No hidden stationary response remains in the two-step formula.

---

# 7. What is still open

The remaining obstacle is **not** the identification of the remote defect, construction of the restricted scan, finite-step stationarity, or extraction of the terminal term. Those steps are already formalized.

The open quantitative problem is now:

```text
control
  sum_{physical e}
    Q^n(RemoteAggregateVariation)(Sum.inl e)

uniformly in periodic volume,
```

and convert the resulting fixed-right response family into a physical remote influence/residual column.

A proof that simply applies the generic dense distinct-fiber coefficient to every physical link will recreate a `card Link` factor and is therefore not sufficient.

The likely successful route must retain one or more of:

```text
bounded Wilson interaction degree,
remote/exceptional support separation,
exact target-ratio response identities,
normalization-aware cross-ratio comparison,
finite-step restricted-scan structure,
source-summed residual / resolvent algebra.
```

The quantitative route must remain non-circular: global C5 contraction cannot be assumed in order to prove the terminal decay used to establish that same contraction.

---

# 8. Current active theorem work

At the time of this documentation refresh, draft PR #4433 is extending the #4421 two-step terminal descent to arbitrary finite scan depth `n` and combining it with the existing arbitrary-step residual column.

That draft is **not theorem authority until merged**.

Its intended interface is

```text
RemoteResponseColumn
<= Q^n(RemoteAggregateVariation)(Sum.inr source)
   + 2 *
     sum_{physical e}
       Q^n(RemoteAggregateVariation)(Sum.inl e).
```

If merged, this will turn the current two-step reduction into a free finite-depth interface and isolate the same aggregate left-mass obstruction at arbitrary `n`.

---

# 9. The volume-independent C5 gate

The geometric gate is already formalized independently of the remaining continuous response estimate.

If

```text
exceptional contribution <= 20 * eta
```

and

```text
remote residual column <= rho,
```

then

```text
column <= 20 * eta + rho.
```

A concrete physical regime satisfying

```text
20 * eta + rho < 1
```

would give the required strict physical column contraction and allow the existing response-certificate / source-resolvent / sweep / coercivity machinery to be instantiated.

At present, the interface is proved; the continuous physical `rho` is not.

---

# 10. Permanent semantic boundaries

These distinctions are part of the repository's proof discipline:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
right-boundary cancellation != arbitrary physical left-left cancellation
one-way represented influence zero != reverse physical influence zero
Sum.inl physical link != Sum.inr represented source
full tagged scan != physical restricted random scan
bounded Wilson degree != decay of ground-state correlations
old dense Harnack majorant != actual bare Wilson interaction graph
exact covariance identity != covariance decay
finite-step response decomposition != volume-uniform contraction
singleton variation != automatically summable propagated variation
finite superposition != contraction
aggregate remote profile != volume-independent bound
response-certificate interface != physical witness existence
uniform finite-volume gap != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion
```

---

# 11. Near-term development order

The preferred theorem order from merged baseline #4421 is:

```text
1. complete arbitrary-n terminal descent and merge only after exact-head GREEN;

2. strengthen the remote response column to allow target-indexed worst-case
   SU(N) values, rather than one common g1,g2,h,k for all targets;

3. isolate a normalization-aware fixed-right response / cross-ratio influence
   interface whose targetwise coefficient is linear in the proved response,
   not a uniform constant summed over all remote targets;

4. prove a sparse/local bound for the aggregate propagated physical-left mass
   using bounded Wilson geometry or an independently established response
   recursion, without the dense all-links majorant;

5. obtain a genuine volume-uniform remote column constant rho;

6. combine rho with the exceptional contribution 20*eta;

7. prove a physical parameter regime with 20*eta + rho < 1;

8. instantiate the existing continuous response certificate and reuse the
   source-resolvent / sweep / coercivity route;

9. derive a volume-uniform finite-volume transfer gap;

10. only then address thermodynamic/scaling-limit physical Yang--Mills
    existence and the final mass-gap statement.
```

See [`ROADMAP.md`](ROADMAP.md) for the phase-by-phase dependency graph.
