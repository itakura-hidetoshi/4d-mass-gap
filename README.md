# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, conditional expectations, quantitative mixing, coercivity, and the mass-gap problem.

The repository deliberately separates exact finite-volume theorems, continuous-state realizations, generic comparison algebra, physical finite-step transport, thermodynamic/continuum passages, and the final Clay-level target.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The continuous C5 `SU(N)` lane has now passed an important structural bridge. The bare Wilson geometry is bounded-degree; outside the C5 exceptional set the local Wilson distortion cancels; the remaining remote defect is a covariance under a normalized fixed-right ground-state kernel-section law; that law has now been rewritten pointwise through the canonical continuous vacuum, factored into a raw one-slab probability law followed by a continuous-vacuum Doob reweighting, and equipped with exact one-link expectation/covariance response identities.
>
> The remaining quantitative problem is **not** to rediscover a one-link law and is **not** to interpret the old dense Harnack coefficient as physical interaction degree. The immediate frontier is to turn the exact remote covariance into a fixed-right response recursion, derive a geometry-sensitive/summable response profile without circularly assuming the desired global contraction, and obtain a volume-independent remote residual column `rho`.

---

## Repository authority — 2026-09-17 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem-carrier branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest theorem-bearing canonical merge:
  ec3e096fb84c56418f5f6d79e7db0ad33d93deeb

Tree:
  140f35101de05e47fac897f6df02c75fab76ca71

Latest merged theorem PR:
  #4335
  Isolate remote C5 response in the vacuum Doob factor

Exact GREEN proof head:
  695d663515be92eefeb502c9a725bcab23c7d66f

Validation receipt:
  PR Lean Fast Check #14044
  workflow run 35149786951
  completed / success

Public landing branch:
  main
```

PR numbering is not merge order: #4337, #4339, and #4342 were already merged before the rebased #4335 was finally merged. The canonical SHA above, not the PR number, is the authority boundary.

The authority order is fixed:

```text
1. exact canonical GitHub SHA on the theorem-carrier branch
2. formal Lean artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

`main` is a public landing surface, not theorem authority when histories differ. Before theorem work, fresh-fetch the theorem-carrier branch rather than trusting this document's recorded SHA.

---

# Current proof spine

```text
FINITE WILSON / OS ROOT
  periodic-even compact SU(N) Wilson model
  -> reflection positivity / OS carriers
  -> one-slab transfer and positive ground-state structure
  -> spatial conditional-expectation / coercivity routing
                                                        [INTEGRATED]

SAME-ROOT SCALAR CONTINUUM OS LANE
  finite Wilson scalar readout
  -> continuum scalar law
  -> reflection positivity
  -> OS Hilbert carrier / C0 semigroup / Hamiltonian
                                                        [INTEGRATED]

CONTINUOUS C5 PHYSICAL PROCESS
  literal normalized continuous SU(N) fiber law
  -> exact right-boundary off-target cancellation
  -> measurable heat-bath update
  -> deterministic schedules
  -> actual restricted random scan over Sum.inl fibers only
  -> finite-step physical boundary-response residual
                                                        [INTEGRATED]

LOCAL GEOMETRY
  off-target local-factor invariance
  -> direct spatial active-neighbor degree <= 18
  -> C5 exceptional background set <= 20
  -> outside exceptional set, local Wilson four-point distortion cancels
                                                        [INTEGRATED]

REMOTE DEFECT LOCALIZATION
  remaining full C5 defect = canonical vacuum defect
  -> fixed-right kernel-section weight w_C(A) = Omega_eig(A) * K(A,C)
  -> normalized probability nu_C
  -> remote defect = explicit factors * Z_C^2 * Cov_{nu_C}(target,source)
                                                        [INTEGRATED]

CONTINUOUS KERNEL-SECTION / FIBER LAW
  Omega_eig density -> canonical Omega_cont density
  -> pointwise one-link section factorization
  -> cancel fixed positive base kernel after normalization
  -> raw one-slab local probability law
  -> exact normalized Doob composition
  -> off-target C5 reference/heat-bath law = raw law reweighted by Omega_cont
                                                        [INTEGRATED]

REMOTE COMMON-RAW DECOMPOSITION
  remote background update, distinct from fiber and sharing no spatial plaquette
  -> raw one-slab weight unchanged
  -> normalized raw law unchanged
  -> two remote C5 laws = two vacuum Doob reweightings of one common raw law
                                                        [INTEGRATED, #4335]

VACUUM RESPONSE IDENTITIES
  E_{nu_C}[localFactor_g] = Omega(C[target<-g]) / Omega(C)
  -> right-boundary update = normalized local-factor tilt
  -> expectation response = covariance / expected tilt
  -> two-source response = source-crossing covariance / expected crossing ratio
                                                        [INTEGRATED, #4337/#4339/#4342]

VOLUME-INDEPENDENT C5 GATE
  exceptional contribution <= 20 * eta
  remote residual column <= rho
  -> column <= 20 * eta + rho
  -> 20 * eta + rho < 1 gives strict contraction
                                                        [INTEGRATED INTERFACE]

QUANTITATIVE FRONTIER
  remote covariance
  -> exact fixed-right response difference
  -> geometry-sensitive recursive response / resolvent profile
  -> volume-independent summable residual column rho
                                                        [OPEN NOW]

DOWNSTREAM
  strict physical response certificate
  -> physical Poincare / coercivity
  -> uniform finite-volume transfer gap
  -> thermodynamic/scaling-limit physical carrier
  -> sufficiently rich 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
                                                        [OPEN]
```

---

# 1. What changed after the #4270 covariance localization

The #4270 stage had already separated the bare Wilson geometry from the global ground-state contribution. The old dense coefficient

```text
(card Link - 1) * offFiberInfluence(beta)
```

remains a valid majorant, but it is not the sharp interaction graph. Direct spatial Wilson interaction has active-neighbor degree at most `18`; adding the resampled fiber and distinguished target gives a C5 exceptional set of cardinality at most `20`.

Outside that set, the target-local factor and raw one-slab four-point distortion cancel exactly. The remaining remote defect is a probability covariance under the fixed-right ground-state kernel-section law `nu_C`.

What was missing at that point was an exact one-link presentation of `nu_C` suitable for response recursion. That bridge is now formalized.

---

# 2. Fixed-right kernel-section law is now an explicit one-link Doob law

The integrated chain from #4294 through #4333 proves, without identifying the law with an RCD or a full Wilson Gibbs conditional, that:

```text
fixed-right ground-state kernel-section probability
  -> canonical continuous-vacuum density presentation
  -> exact pointwise one-link section
  -> removal of the fixed positive base-kernel constant
  -> raw one-slab local Boltzmann probability law
  -> continuous-vacuum Doob reweighting of that raw law.
```

In particular, for off-target C5 fibers the literal reference-fiber measure and the already-existing conditional/heat-bath machinery are connected to this raw-vacuum Doob representation. This closes the earlier semantic gap between the probability-covariance localization and the measurable one-link C5 process.

---

# 3. PR #4335: remote changes share one raw local law

If a changed background link is distinct from the resampled fiber and shares no spatial Wilson plaquette with it, then the exact raw one-slab link weight is unchanged. Consequently the normalized raw one-slab link law is unchanged as well.

Therefore two remote background values have the form

```text
Doob_{Omega_u}(nu_raw)
Doob_{Omega_v}(nu_raw)
```

with the **same** raw one-slab probability measure `nu_raw`.

This is an exact measure-level isolation of the nonlocal part: under the remote hypotheses, all remaining dependence on the changed background value sits in the canonical continuous-vacuum fiber weight.

This theorem does **not** itself prove that the vacuum response is small or decays with distance.

---

# 4. The vacuum response is now an exact local expectation/covariance response

The fixed-right probability family now satisfies three complementary exact identities.

## 4.1 Vacuum ratio as one-link expectation — #4337

For the literal one-slab right-target local factor `L_g`,

```text
E_{nu_C}[L_g]
  = Omega(C[target <- g]) / Omega(C).
```

Thus a global one-link vacuum ratio is represented by the expectation of an explicit local Wilson observable under `nu_C`.

## 4.2 Right-boundary update as a local tilt — #4339

Changing one right-boundary link produces a normalized tilt by the corresponding local factor. For an admissible real observable `F`, the expectation response is

```text
E_{nu_{C_g}}[F] - E_{nu_C}[F]
  = Cov_{nu_C}(L_g, F) / E_{nu_C}[L_g].
```

The denominator is positive by the preceding vacuum-ratio identity.

## 4.3 Two-source response as crossing covariance — #4342

For two values `h,k` of one fixed right-boundary source, the `A`-independent spatial half-action factor cancels. The response becomes

```text
E_{nu_{B[source <- h]}}[F]
- E_{nu_{B[source <- k]}}[F]
  = Cov_{nu_{B[source <- k]}}(crossingRatio_{h/k}, F)
    / E_{nu_{B[source <- k]}}[crossingRatio_{h/k}].
```

The source observable here is exactly the source-crossing observable already appearing in the remote C5 covariance residual.

---

# 5. The current open theorem is now one step later

The repository no longer needs a speculative bridge from `nu_C` to one-link response machinery: that bridge exists.

The immediate next coherent unit is to combine the existing remote-defect identity

```text
remote defect
  = sourceSpatialRatio
    * Z_C^2
    * Cov_{nu_C}(targetLocalRatio, sourceCrossingRatio)
```

with the #4342 response identity, producing an exact **remote defect = fixed-right expectation response** formula with all normalization factors explicit.

After that, the hard quantitative task is to derive a non-circular recursive inequality for those fixed-right responses whose propagation respects Wilson geometry. The target is a profile that can be summed uniformly in periodic volume:

```text
remote response
  -> geometry-sensitive recursion / resolvent
  -> summable residual(target,source)
  -> sup_source sum_remote residual(target,source) <= rho
  -> column <= 20 * eta + rho.
```

A uniform pairwise bound followed by summation over every remote link is not sufficient; it would simply recreate a volume factor.

---

# 6. Existing volume-independent contraction interface

The abstract geometric gate is already formalized. If

```text
sum_target influence(target,source)
  <= 20 * eta + sum_target residual(target,source)
```

and

```text
sum_target residual(target,source) <= rho
```

uniformly in source, then

```text
columnSum <= 20 * eta + rho.
```

Hence

```text
20 * eta + rho < 1
```

is sufficient for strict column contraction.

What remains missing is the concrete continuous-`SU(N)` physical value/bound `rho` obtained from the newly exposed vacuum-response recursion.

---

# 7. Physical scan semantics remain restricted

The represented carrier uses

```text
Sum.inl fiber  = physical left fiber that may be heat-bath updated
Sum.inr source = represented right-boundary source parameter.
```

Only `Sum.inl` coordinates are physical scan targets. `Sum.inr` coordinates are static bookkeeping/source coordinates. The actual restricted random scan, measurable finite-step expectation iterate, and geometric forcing residual are already formalized.

---

# 8. Permanent semantic boundaries

The following distinctions remain part of the proof discipline:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
right-boundary exact cancellation != arbitrary left-left cancellation
common raw remote law != small vacuum response
Doob representation != regular conditional probability identification
probability normalization != Gibbs independence
crossing-covariance identity != covariance decay
response recursion interface != proved summability
bounded local degree != decay of the global ground-state contribution
old dense Harnack majorant != actual bare Wilson interaction graph
finite-step physical transport != volume-uniform contraction
state-space-independent certificate interface != physical witness existence
uniform finite-volume gap != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion
```

Z2-specific decay results may serve as structural references but are not evidence for the required continuous `SU(N)` estimate.

---

# 9. Near-term development order

Starting from canonical

```text
ec3e096fb84c56418f5f6d79e7db0ad33d93deeb
```

the preferred theorem sequence is:

```text
1. rewrite the exact remote C5 probability covariance as a fixed-right
   expectation response using the already-merged #4342 identity;

2. derive the corresponding response propagation/recursion while keeping
   the bounded Wilson interaction geometry explicit;

3. solve/bound that recursion with the existing finite
   Dobrushin/resolvent/geometric-support machinery, without assuming the
   global C5 contraction being proved;

4. prove a volume-independent remote residual-column bound rho;

5. combine it with the already-proved exceptional-set gate
   column <= 20 * eta + rho;

6. if 20 * eta + rho < 1, instantiate the actual continuous physical
   response certificate and continue to coercivity and the finite-volume gap.
```

The present boundary is therefore sharper than the previous documentation: **the one-link kernel-section/Doob bridge is no longer open. The open problem is the quantitative, geometry-sensitive propagation and summability of the now-exact vacuum response.**
