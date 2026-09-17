# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, conditional expectations, quantitative mixing, coercivity, and the mass-gap problem.

The repository is organized so that exact finite-volume theorems, continuous-state realizations, comparison/response algebra, physical C5 transport, coercivity routing, continuum limits, and the final Clay-level target remain logically separated.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current continuous `SU(N)` C5 lane has now moved beyond the earlier dense all-links Harnack majorant. The local Wilson geometry is bounded-degree; remote four-point defects are reduced to a normalized fixed-right ground-state kernel-section probability problem; source updates are converted exactly into fixed-right expectation responses; and the literal target-ratio response is now propagated through the actual stationary restricted C5 random scan to a finite-step source-transport-plus-terminal residual.
>
> The immediate quantitative problem is to close that exact finite-step residual into a **volume-independent remote column bound** `rho`, without reintroducing a factor proportional to the number of spatial links and without assuming the global contraction that the argument is intended to prove.

---

## Repository authority — documentation baseline 2026-09-17 JST

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The theorem-bearing baseline used for this documentation refresh is

```text
37b3caa7b20344d0ba8b4951ae93719190da4814
```

with tree

```text
bc5c85cfe0804eb4076325c170e2b7d57cfa6c4a
```

This is the merge of PR #4367:

```text
Specialize stationary C5 residual to fixed-right target ratio
```

Exact GREEN proof head:

```text
686c673a776d0b9fc819e6b6834a3db2ab17a60a
```

Validation receipt:

```text
PR Lean Fast Check #14071
workflow run 35211640508
completed / success
```

This documentation update is docs-only. Once it is merged, the theorem-carrier branch pointer will advance even though the theorem-bearing Lean baseline remains #4367 until the next theorem merge. Therefore **always fresh-fetch the branch before theorem work**; do not treat a SHA printed in README or ROADMAP as live authority.

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
  -> measurable heat-bath sampling and reinsertion
  -> exact right-boundary off-target cancellation
  -> sharp surviving diagonal right-source coefficient
                                                        [INTEGRATED]

PHYSICAL MULTI-STEP TRANSPORT
  same-fiber + distinct-fiber transport
  -> deterministic schedules
  -> actual restricted random scan over physical Sum.inl fibers
  -> finite-step measurable expectation iterate
  -> tagged physical variation transport
                                                        [INTEGRATED]

LOCAL C5 GEOMETRY
  target-local-factor locality
  -> active-neighbor degree <= 18
  -> C5 exceptional set <= 20
  -> outside exceptional set, local Wilson four-point distortion cancels
                                                        [INTEGRATED]

GROUND-STATE KERNEL-SECTION PROBABILITY
  w_C(A) = Omega(A) * K(A,C)
  -> positive finite mass
  -> normalized fixed-right probability law nu_C
  -> remote weighted defect = explicit factors * Cov_{nu_C}
                                                        [INTEGRATED]

FIXED-RIGHT SOURCE RESPONSE
  one-link vacuum update = fixed-right expectation
  -> right update = normalized tilt
  -> two-source response = crossing covariance / crossing mean
  -> remote C5 covariance = fixed-right target-ratio response
                                                        [INTEGRATED THROUGH #4355]

STATIONARY RESTRICTED C5 RESPONSE
  exact reference-law stationarity
  -> finite-step response recursion
  -> literal target-ratio specialization
  -> singleton target variation exp(16*beta), zero off target
                                                        [INTEGRATED THROUGH #4367]

VOLUME-INDEPENDENT C5 GATE
  exceptional contribution <= 20 * eta
  remote residual column <= rho
  20 * eta + rho < 1
  -> strict physical column contraction
                                                        [INTEGRATED INTERFACE]

QUANTITATIVE FRONTIER
  close the #4367 finite-step target-ratio residual into
  a volume-independent remote response/residual column bound rho
                                                        [OPEN NOW]

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

Several potentially volume-growing steps have now been isolated or removed.

## 1.1 Exact represented right-source locality

For the literal continuous C5 one-link law, a represented right-boundary source distinct from the resampled physical fiber changes the unnormalized density only by a positive scalar independent of the integration variable. Normalization cancels that scalar exactly.

Only the matching represented source survives, with

```text
q(beta)
  = 2 * (exp(16*beta) - 1) / (exp(16*beta) + 1).
```

Hence for

```text
0 <= beta < log 3 / 16
```

one has `q(beta) < 1` without a spatial-volume factor.

## 1.2 Bounded bare Wilson geometry

For a spatial link, the number of distinct intrinsic spatial links sharing a spatial Wilson plaquette is at most

```text
18.
```

After adding the resampled fiber and distinguished right target, the C5 exceptional set has cardinality at most

```text
20
```

uniformly in periodic volume.

This is a theorem about **bare/local Wilson geometry**. It is not by itself a theorem about decay of the globally synthesized ground state.

## 1.3 The old dense majorant remains valid but is not the geometry

The older coefficient

```text
(card Link - 1) * offFiberInfluence(beta)
```

is still a correct all-links majorant obtained by assigning the same off-fiber estimate to every distinct link. It should not be interpreted as evidence that the Wilson action has dense direct spatial interaction.

---

# 2. Remote defects are now fixed-right probability responses

Outside the exceptional set, the target-local factor and raw slab four-point Wilson distortion cancel exactly. The remaining defect is a ground-state contribution.

The relevant weight is rewritten as a fixed-right kernel section

```text
w_C(A) = Omega(A) * K(A,C),
```

with positive finite mass

```text
Z_C = integral w_C dmu > 0,
```

so it defines a probability law

```text
nu_C = w_C dmu / Z_C.
```

The remote weighted covariance numerator is therefore exactly

```text
Z_C^2 * Cov_{nu_C}(targetObservable, sourceObservable).
```

The later fixed-right response chain sharpens this further:

```text
#4337  one-link vacuum response -> kernel-section expectation
#4339  one right-boundary update -> local covariance response
#4342  two-source response -> crossing covariance / crossing mean
#4345  specialization to the literal remote target ratio
#4348  full remote reference law = exact fixed-right kernel-section law
#4353  remote C5 covariance -> fixed-right expectation response
#4355  exceptional-set remote residual -> fixed-right response
```

Thus the remaining nonlocal problem is no longer merely “identify the covariance.” It is to **quantitatively bound the exact fixed-right response** in a form that is summable uniformly in volume.

---

# 3. The actual stationary C5 response is now formalized

PRs #4360, #4363, and #4367 connect the fixed-right response to the real continuous C5 dynamics.

The physical scan is restricted:

```text
Sum.inl fiber  = physical left fiber that may be updated
Sum.inr source = represented right-boundary source parameter
```

Only `Sum.inl` coordinates are scanned. `Sum.inr` coordinates remain static source labels.

For the literal fixed-right target-ratio observable

```text
F_target(A)
  = localFactor(A,target,g1) / localFactor(A,target,g2),
```

#4367 proves positivity, strong measurability, integrability, and the singleton coordinate-variation profile

```text
variation_target(e)
  = exp(16*beta)   if e = target,
    0              otherwise.
```

For a remote target/source pair, the response between source values `h` and `k` is bounded schematically by

```text
fixedRightResponse(target, source; h, k)
  <= taggedRestrictedScanVariationIterate(
       variation_target, n, Sum.inr source)
     + terminalResponseAfterNSteps.
```

This is an exact finite-step theorem for the actual stationary restricted continuous-C5 process. No volume-growing initial variation is inserted: the initial observable variation is supported only at the physical target.

What is **not** yet proved is that the right-hand side has a remote-column sum bounded by a volume-independent constant `rho`.

---

# 4. Current quantitative frontier

The next theorem unit must close the finite-step residual without circularity.

The desired output is a bound of the form

```text
sup_source
  sum_{remote target}
    remoteResidual(target, source)
<= rho
```

where `rho` is independent of periodic volume.

A pointwise estimate followed by summation over every remote target is not sufficient if it recreates a factor comparable to `card Link`.

The present decomposition shows exactly what must be controlled:

```text
A. accumulated tagged transport from a singleton target variation;
B. the terminal difference of the common k-smoothed target-ratio observable.
```

A successful route must prove summability/decay for these terms from already available local/transfer structure, rather than assume the final global C5 contraction.

Once a concrete `rho` is obtained, the already-formalized geometric gate gives

```text
column <= 20 * eta + rho.
```

If one proves

```text
20 * eta + rho < 1,
```

then the physical strict column contraction can be instantiated and the existing response/resolvent/coercivity route can be re-entered.

---

# 5. Why #4367 is a genuine advance over the #4270 frontier

At #4270 the remote problem had been localized to a ground-state probability covariance, but the connection from that covariance to the actual C5 dynamics was still missing.

The current chain now supplies that bridge:

```text
remote physical defect
-> normalized fixed-right probability covariance
-> exact fixed-right source response
-> stationary restricted C5 finite-step response
-> singleton-supported physical variation transport
   + terminal response.
```

So the frontier is no longer “find a probabilistic interpretation” or “construct a physical scan.” Both are already in the theorem chain. The frontier is the **quantitative closure of the exact residual**.

---

# 6. Permanent semantic boundaries

The following distinctions are part of the proof discipline and should remain visible in future extensions:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
right-boundary exact cancellation != arbitrary left-left cancellation
one-way tagged zero block != reverse physical influence zero
Sum.inl link != Sum.inr source
full tagged random scan != physical restricted random scan
old dense Harnack majorant != actual bare Wilson interaction graph
bounded local degree != decay of ground-state correlations
probability normalization != Gibbs/RCD or conditional-independence theorem
exact covariance identity != covariance decay
finite-step response decomposition != volume-uniform contraction
singleton initial variation != summable propagated variation automatically
state-space-independent certificate interface != physical witness existence
uniform finite-volume gap != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion
```

---

# 7. Near-term development order

From theorem-bearing baseline #4367, the preferred sequence is:

```text
1. analyze the tagged restricted-scan iterate generated by the singleton
   target variation exp(16*beta);

2. obtain a non-circular control of the terminal fixed-right response after
   n stationary scan steps;

3. combine the two terms into a geometry-sensitive remote response bound;

4. sum the remote column uniformly in periodic volume to obtain rho;

5. transport that response bound back through #4353/#4355 to the physical
   C5 residual;

6. combine with the exceptional-set bound 20*eta;

7. prove a parameter regime with 20*eta + rho < 1;

8. instantiate the concrete continuous response certificate and reuse the
   existing source-resolvent / sweep / coercivity machinery;

9. continue toward a uniform finite-volume physical transfer gap and only
   then address the thermodynamic/continuum physical limit.
```

See [`ROADMAP.md`](ROADMAP.md) for the phase-by-phase dependency graph and explicit open gates.
