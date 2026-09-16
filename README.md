# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, conditional expectations, quantitative mixing, coercivity, and the mass-gap problem.

The repository deliberately separates exact finite-volume theorems, continuous-state realizations, generic comparison algebra, physical finite-step transport, thermodynamic/continuum passages, and the final Clay-level target.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The continuous C5 `SU(N)` lane now goes substantially beyond the earlier all-to-all Harnack majorant. The actual physical restricted random scan and its finite-step response residual are formalized. More importantly, the local Wilson geometry has now been separated from the genuinely nonlocal ground-state contribution: direct spatial Wilson interaction has uniformly bounded degree, the C5 exceptional background set has cardinality at most `20`, and outside that set the remaining four-point defect is exactly an ordinary covariance of two one-link observables under a normalized fixed-right ground-state kernel-section probability law.
>
> The immediate open problem is therefore no longer to interpret
>
> ```text
> (card Link - 1) * offFiberInfluence(beta)
> ```
>
> as a physical interaction degree. That expression remains a correct coefficient for the older dense majorant, but it is **not evidence of dense bare Wilson coupling**. The current quantitative frontier is to prove a **volume-independent summable bound on the remote ground-state probability-covariance residual** and feed that bound into the already-formalized C5 column and resolvent machinery.

---

## Repository authority — 2026-09-16 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem-carrier branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest theorem-bearing canonical merge:
  5c392b82ef522006885740ad85588a792d340a2a

Tree:
  75bc12fa5f2e2dae613e3f051a89fff470522310

Merged PR:
  #4270
  Sharpen C5 distinct-background Harnack off target

Exact GREEN proof head:
  236e9d0e31b88c7ca103915ea8dd38b0e5e41f21

Validation receipt:
  PR Lean Fast Check #13994
  workflow run 35086312903
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

`main` is a public landing surface, not theorem authority when histories differ. Before theorem work, fresh-fetch the theorem-carrier branch rather than trusting this document's recorded SHA.

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
  literal normalized continuous SU(N) fiber law
  -> measurable heat-bath sampling and reinsertion
  -> exact right-boundary off-target cancellation
  -> sharp surviving diagonal right-source coefficient
                                                        [INTEGRATED]

PHYSICAL MULTI-STEP TRANSPORT
  same-fiber + distinct-fiber two-step transport
  -> deterministic schedules
  -> actual restricted random scan over Sum.inl fibers only
  -> finite-step measurable expectation iterate
  -> physical boundary-response geometric residual
                                                        [INTEGRATED]

LOCAL GEOMETRY SHARPENING
  exact off-target target-local-factor invariance
  -> raw off-target Harnack exp(32 beta) -> exp(16 beta)
  -> direct spatial active-neighbor degree <= 18
  -> C5 exceptional background set <= 20
                                                        [INTEGRATED]

REMOTE DEFECT ISOLATION
  outside exceptional set:
  local target factor cancels exactly
  + raw slab cross-ratio cancels exactly
  -> remaining full C5 defect = canonical vacuum defect
  -> exact weighted covariance normal form
                                                        [INTEGRATED]

GROUND-STATE KERNEL-SECTION PROBABILITY
  w_C(A) = Omega_eig(A) * K(A,C)
  -> exact kernel-section identity
  -> integrable / a.e. nonnegative
  -> total mass = ||T|| * Omega_cont(C) > 0
  -> normalized probability measure nu_C
  -> remote defect = explicit factors * mass^2 * Cov_{nu_C}(local,target)
                                                        [INTEGRATED THROUGH #4270]

VOLUME-INDEPENDENT C5 GATE
  influence column <= 20 * eta + residual-column
  residual-column <= rho
  20 * eta + rho < 1
  -> strict column contraction
                                                        [INTEGRATED INTERFACE]

QUANTITATIVE FRONTIER
  prove a concrete volume-independent bound on
  the remote ground-state probability-covariance residual
  without reintroducing an all-links volume factor
                                                        [OPEN NOW]

DOWNSTREAM
  covariance/residual summability
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

# 1. Two influence mechanisms remain distinct

## 1.1 Represented right-boundary source -> left target

For the literal C5 one-link law, a right-boundary source distinct from the resampled fiber changes the unnormalized density by a positive scalar independent of the integration variable. The scalar cancels in normalization. Hence the normalized fiber laws, conditional kernels, and heat-bath kernels agree exactly off target.

Only the matching source survives, with

```text
q(beta)
  = 2 * (exp(16*beta) - 1) / (exp(16*beta) + 1).
```

Thus the represented right-source row is one-point supported and, for

```text
0 <= beta < log 3 / 16,
```

one has `q(beta) < 1` without a spatial-volume factor.

## 1.2 Physical left background -> another physical left update

This is the genuine composition problem. Earlier the distinct-fiber comparison was bounded uniformly by an off-fiber Harnack coefficient, producing

```text
(card Link - 1) * offFiberInfluence(beta)
```

after summing over all distinct targets.

That theorem remains valid as a dense majorant. PR #4270 shows why it is not the sharp geometric description of the Wilson interaction.

---

# 2. What PR #4270 changes

## 2.1 Off-target raw Harnack is sharper

When the changed background fiber is not the distinguished target, the exact target-local factor is unchanged. The raw reference-weight Harnack cost therefore drops from

```text
exp(32 * beta)
```

to

```text
exp(16 * beta).
```

This sharpening alone still does not prove remote normalized influence is zero, because the canonical ground state is globally synthesized.

## 2.2 Bare spatial Wilson geometry has bounded degree

For a spatial link, the set of distinct intrinsic spatial links sharing a spatial Wilson plaquette with it has cardinality at most

```text
18.
```

Adding the resampled fiber itself and the distinguished right target gives the C5 exceptional background set

```text
exceptional(fiber,target)
  = {fiber, target} union activeNeighbors(fiber),
```

with

```text
card exceptional(fiber,target) <= 20
```

uniformly in periodic volume.

So the direct local Wilson geometry is bounded-degree, not all-to-all.

## 2.3 Outside the exceptional set, local Wilson factors cancel exactly

If a background fiber lies outside the exceptional set, then it

```text
is distinct from the resampled fiber,
is distinct from the distinguished target,
and shares no spatial Wilson plaquette with the resampled fiber.
```

Under exactly these hypotheses, the target-local factor and the raw slab four-point distortion cancel. The full literal C5 reference-weight four-point defect is reduced exactly to the canonical continuous-vacuum defect.

This is a structural cancellation theorem, not a decay assumption.

---

# 3. Remote vacuum defect is now a probability covariance

The remaining remote defect is first written as a weighted covariance numerator of two one-link observables. The relevant weight can then be rewritten exactly as a fixed-right ground-state kernel section

```text
w_C(A)
  = Omega_eig(A) * K(A,C).
```

Here `K` is the one-slab kernel and `C` is the doubly updated right boundary.

The formalization proves that this weight is integrable and a.e. nonnegative, with positive exact total mass

```text
Z_C
  = integral w_C dmu
  = ||T|| * Omega_cont(C)
  > 0.
```

Therefore it defines a genuine probability law

```text
nu_C = w_C dmu / Z_C.
```

The unnormalized covariance numerator satisfies the exact normalization identity

```text
WeightedCovarianceNumerator(w_C; f,g)
  = Z_C^2 * Cov_{nu_C}(f,g).
```

Consequently, outside the C5 exceptional set, the remaining remote four-point defect has the form

```text
sourceSpatialRatio
* Z_C^2
* Cov_{nu_C}(
    target-local-factor ratio,
    source Wilson-crossing ratio).
```

No regular-conditional-probability identification and no Gibbs-independence claim is needed for this theorem.

---

# 4. The new volume-independent column interface

The geometric decomposition is packaged abstractly as follows. If a physical influence column obeys

```text
influence(target,source)
  <= [eta on exceptional(source)] + residual(target,source),
```

then, because the exceptional set has size at most `20`,

```text
sum_target influence(target,source)
  <= 20 * eta
     + sum_target residual(target,source).
```

If the remote residual column has a uniform bound

```text
sum_target residual(target,source) <= rho,
```

then

```text
columnSum <= 20 * eta + rho.
```

Hence

```text
20 * eta + rho < 1
```

is a sufficient volume-independent strict-contraction gate.

This gate is formalized. What is **not** yet formalized is a concrete physical `rho` for the continuous `SU(N)` ground-state probability covariance.

---

# 5. Current theorem-development frontier

The next hard theorem is a **summable remote covariance estimate** for the family of fixed-right probability laws `nu_C`.

The target is not a uniform bound of the form

```text
|Cov_{nu_C}(f_target,g_source)| <= constant
```

followed by summation over all remote links, because that would simply recreate a volume factor.

The desired route is instead a geometry-sensitive estimate whose total remote column is uniformly summable, for example through a proved distance/resolvent profile:

```text
remote covariance
  -> distance-sensitive or kernel-resolvent bound
  -> summable residual column rho
  -> 20 * eta + rho < 1
  -> restricted-scan contraction.
```

The repository already contains generic finite Dobrushin / resolvent / geometric-support machinery. The missing bridge is a non-circular theorem that connects the continuous ground-state kernel-section probability covariance to that machinery.

A preferred route is to exploit the canonical continuous vacuum representative and its a.e. equality with the existing top-eigenvector `L²` class, together with the already-formalized one-link continuous-vacuum Doob laws. Any such bridge must avoid assuming the same global C5 contraction that it is intended to prove.

Z2-specific covariance-decay results are not evidence for the continuous `SU(N)` result and must not be imported as if they were.

---

# 6. Why the physical scan remains restricted

The represented carrier uses

```text
Sum.inl fiber  = physical left fiber that may be heat-bath updated
Sum.inr source = represented right-boundary source parameter.
```

Only `Sum.inl` coordinates are physical scan targets. `Sum.inr` coordinates are static bookkeeping/source coordinates. This is encoded in the actual process, not merely an interpretation.

The finite-step chain already formalized is

```text
#4249 generic restricted-target random scan
#4252 actual physical continuous C5 restricted random scan
#4254 measurable one-step affine transport
#4257 finite-step physical expectation iterate and domination
#4260 generic restricted-target geometric forcing residual
#4266 physical C5 specialization
#4270 geometric sharpening and ground-state covariance localization.
```

---

# 7. Permanent semantic boundaries

The following distinctions remain part of the proof discipline:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
right-boundary exact cancellation != arbitrary left-left cancellation
one-way tagged zero block != reverse physical influence zero
Sum.inl link != Sum.inr link
full tagged random scan != physical restricted random scan
old dense Harnack majorant != actual bare Wilson interaction graph
bounded local degree != decay of the ground-state covariance residual
probability normalization != conditional-independence theorem
geometric residual formula != geometric decay without a rate < 1
finite-step physical transport != volume-uniform contraction
state-space-independent certificate interface != physical witness existence
uniform finite-volume gap != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion
```

---

# 8. Near-term target

Starting from theorem-bearing canonical merge

```text
5c392b82ef522006885740ad85588a792d340a2a
```

the preferred next sequence is:

```text
1. use the canonical continuous vacuum representative to rewrite the
   fixed-right kernel-section probability density without exceptional
   pointwise L2-representative ambiguity;

2. connect its one-link conditional response to the existing physical
   continuous-vacuum Doob / Wilson one-link machinery;

3. derive a non-circular geometry-sensitive covariance/resolvent estimate;

4. prove a volume-independent remote residual-column bound rho;

5. combine it with the already-proved exceptional-set gate
   column <= 20*eta + rho;

6. if 20*eta + rho < 1 is obtained, instantiate the actual continuous
   response certificate and re-enter the resolvent/coercivity route.
```

The repository therefore stands at a sharper boundary than after #4266: the **bare Wilson locality problem has been separated from the global ground-state problem**. The immediate unresolved quantity is the **summability of the ground-state kernel-section probability covariance residual**.
