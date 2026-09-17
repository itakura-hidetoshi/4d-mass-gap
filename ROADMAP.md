# MGAP4D Roadmap

This roadmap records the current theorem architecture and development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-17 JST**.

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
bc5c85cfe0804eb4076325c170e2b7d57cfa6c4a.
```

This is the merge of PR #4367,

```text
Specialize stationary C5 residual to fixed-right target ratio
```

from exact GREEN proof head

```text
686c673a776d0b9fc819e6b6834a3db2ab17a60a
```

validated by

```text
PR Lean Fast Check #14071
workflow run 35211640508
completed / success.
```

This file is documentation, not live theorem authority. A docs-only merge can advance the authoritative branch pointer without changing the theorem-bearing Lean baseline. Before theorem work, fresh-fetch the branch and re-establish the exact current SHA.

Authority order:

```text
exact current canonical GitHub SHA
-> formal Lean artifacts
-> README / ROADMAP
-> CI/runtime receipts
-> historical summaries or memory.
```

> **Current frontier**
>
> The main structural bridge that was missing after PR #4270 is now integrated. Remote continuous-C5 defects are not only reduced to a fixed-right ground-state probability covariance: they are converted exactly to a fixed-right source response, and that response is propagated through the actual stationary restricted continuous-C5 random scan to a finite-step residual.
>
> PR #4367 specializes the residual to the literal target-local-factor ratio and gives it a singleton physical coordinate-variation profile of magnitude `exp(16*beta)` at the target and zero elsewhere.
>
> The immediate open problem is now to turn
>
> ```text
> tagged finite-step transport + terminal response
> ```
>
> into a **volume-independent remote column bound** `rho`, and then combine it with the already-formalized exceptional-set gate
>
> ```text
> column <= 20 * eta + rho.
> ```
>
> No strict continuous-SU(N) physical contraction is claimed until a concrete `rho` and a parameter regime satisfying `20 * eta + rho < 1` are proved.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative theorem-carrier history.
- **Integrated routing** — the implication route is formalized, but a quantitative physical input remains open.
- **Integrated interface** — the theorem is proved, but concrete model-derived witnesses remain to be supplied.
- **Obstruction integrated** — a tempting route has been formalized or exposed as insufficient and should not be reused as if it solved the stronger problem.
- **Open now** — immediate theorem-development frontier.
- **Open next** — next coherent unit after the current frontier.
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
  -> spatial conditional-expectation projections
  -> block Poincare/coercivity routing
  -> physical transfer-gap route

D. CONTINUOUS C5 ONE-LINK LAW                                  [INTEGRATED]

normalized continuous SU(N) one-link law
  -> measurable heat-bath sampling and reinsertion
  -> sharp one-link Harnack / variation control
  -> physical one-link Doob bridge

E. RIGHT-BOUNDARY EXACT LOCALITY                               [INTEGRATED]

source != resampled fiber
  -> scalar multiple of common unnormalized weight
  -> normalization cancellation
  -> exact equality of normalized laws / kernels
  -> represented influence exactly zero

source = resampled fiber
  -> q(beta) = 2*(exp(16 beta)-1)/(exp(16 beta)+1)
  -> beta < log 3/16 => q(beta) < 1

F. ONE-WAY TAGGED CARRIER + RESPONSE ALGEBRA                   [INTEGRATED]

Sum.inl target <- Sum.inr source
  -> represented C5 coefficient
  -> source-response / resolvent / sweep interfaces
  -> state-space-independent certificate layer

G. ACTUAL PHYSICAL MULTI-STEP TRANSPORT                        [INTEGRATED]

same-fiber transport
  -> distinct-fiber transport
  -> deterministic schedules
  -> restricted random scan
  -> finite-step measurable expectation iterate
  -> tagged variation propagation

H. LOCAL C5 GEOMETRY SHARPENING                                [INTEGRATED]

target-local-factor locality
  -> active spatial-neighbor degree <= 18
  -> C5 exceptional set <= 20
  -> dense all-links Harnack majorant separated from bare geometry

I. REMOTE WILSON CANCELLATION                                  [INTEGRATED]

outside exceptional set:
  target-local factor cancels
  + raw slab four-point distortion cancels
  -> remaining defect = canonical ground-state/vacuum defect

J. FIXED-RIGHT GROUND-STATE PROBABILITY                        [INTEGRATED]

w_C(A) = Omega(A) * K(A,C)
  -> positive finite mass
  -> normalized probability nu_C
  -> weighted remote defect = Z_C^2 * Cov_{nu_C}

K. FIXED-RIGHT SOURCE-RESPONSE IDENTITIES                      [INTEGRATED]

#4337 one-link vacuum ratio = kernel-section expectation
#4339 right update = normalized local tilt/covariance response
#4342 two-source response = crossing covariance / crossing mean
#4345 specialize to remote target ratio
#4348 remote full reference law = fixed-right kernel-section law
#4353 remote physical covariance = fixed-right expectation response
#4355 exceptional-set remote residual = fixed-right response

L. STATIONARY RESTRICTED C5 RESPONSE                           [INTEGRATED]

#4360 exact stationarity under the restricted continuous-C5 dynamics
#4363 finite-step response <= tagged source transport + terminal response
#4367 literal fixed-right target-ratio specialization
       with singleton variation exp(16 beta) at target and zero elsewhere

M. VOLUME-INDEPENDENT EXCEPTIONAL + RESIDUAL GATE              [INTEGRATED INTERFACE]

exceptional contribution <= 20 * eta
remote residual column <= rho
  -> column <= 20 * eta + rho
  -> 20 * eta + rho < 1 => strict column contraction

N. CLOSE THE #4367 FINITE-STEP RESIDUAL                        [OPEN NOW]

control, without circularity:
  1. tagged restricted-scan propagation from singleton target variation
  2. terminal fixed-right response after n scan steps

then prove a remote-column-summable response bound independent of volume

O. CONCRETE PHYSICAL rho                                       [OPEN NEXT]

transport the fixed-right response estimate back through #4353/#4355
  -> physical remote residual(target,source)
  -> sup_source sum_remote residual <= rho
  -> exhibit regime 20*eta + rho < 1

P. ACTUAL CONTINUOUS RESPONSE CERTIFICATE                      [OPEN NEXT]

strict physical column bound
  + concrete discrepancy/sourceBound witnesses
  -> instantiate response certificate
  -> source resolvent / sweep machinery

Q. PHYSICAL POINCARE / COERCIVITY                              [OPEN DOWNSTREAM]

physical response control
  -> quantitative block coercivity
  -> spatial conditional inequalities

R. UNIFORM FINITE-VOLUME TRANSFER GAP                          [OPEN DOWNSTREAM]

scale-independent kappa_* > 0
  -> physical transfer-gap lower bound

S. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                    [OPEN DOWNSTREAM]

uniform finite-volume gap
  -> limiting physical carrier
  -> OS/Wightman spectral lower bound
  -> sufficiently rich same-root 4D Yang--Mills field/state

T. CLAY-LEVEL EXISTENCE + MASS GAP                             [OPEN]
```

---

# Phase 0 — Authority, CI, and proof discipline

**Status: Integrated and permanent.**

For theorem-bearing work:

```text
fresh-fetch authoritative branch
-> lock exact canonical SHA
-> inspect exact theorem interfaces
-> state the smallest coherent theorem unit
-> run exact-head CI
-> inspect the first genuine Lean error if RED
-> apply the smallest proof-preserving fix
-> require terminal completed/success evidence
-> merge against the expected exact head
-> fresh-fetch the canonical branch again.
```

The GitHub completion push lane is notification infrastructure only. A PR comment containing `CHATGPT_CI_COMPLETION_PUSH_V0_1` is a wake-up signal, not CI truth, merge authority, or write authority. Governed action requires fresh observation of the exact workflow run and exact head SHA. Secondary direct checks may supplement notification delivery, but terminal GitHub state remains authoritative.

Queued or in-progress CI is not GREEN. New `sorry`, `admit`, axioms, assumption weakening, theorem weakening, or semantic broadening are not acceptable substitutes for proof.

Permanent distinctions include:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
right-boundary exact cancellation != arbitrary left-left cancellation
one-way represented influence zero != reverse physical influence zero
Sum.inl physical link != Sum.inr represented source
full tagged scan != physical restricted scan
old dense Harnack majorant != actual Wilson interaction graph
bounded local degree != decay of global ground-state correlations
probability normalization != Gibbs/RCD or conditional independence
exact covariance identity != covariance decay
finite-step response decomposition != volume-uniform contraction
uniform finite-volume gap != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion.
```

---

# Phase 1 — Finite Wilson root and OS infrastructure

**Status: Integrated.**

The finite theorem root contains the periodic-even compact `SU(N)` Wilson construction, lattice geometry, Haar reference measure, Wilson action, reflection positivity, gauge-compatible structures, spatial-slice carriers, one-slab transfer operators, and positive ground-state architecture.

The implication route from spatial conditional estimates to a finite-volume physical transfer gap exists. A model-derived volume-uniform quantitative coefficient remains a downstream obligation.

---

# Phase 2 — Same-root scalar continuum OS lane

**Status: Integrated as a scalar observable lane.**

The repository constructs a continuum scalar law from finite Wilson readouts, establishes continuum reflection positivity, forms an OS Hilbert carrier, and obtains a real strongly continuous contraction semigroup with a self-adjoint Hamiltonian and vacuum structure.

Boundary: this is a same-root scalar continuum lane, not yet the complete four-dimensional Yang--Mills gauge field/state required by the Clay problem.

---

# Phase 3 — Continuous C5 local control and bounded geometry

**Status: Integrated.**

The continuous C5 one-link law supplies measurable normalized heat-bath kernels and sharp one-link comparison control.

For represented right-boundary sources:

```text
source != fiber
-> exact equality of normalized fiber laws
-> exact equality of conditional/heat-bath kernels
-> exact zero represented influence.
```

At `source = fiber`, the surviving coefficient is

```text
q(beta)
  = 2 * (exp(16*beta)-1)/(exp(16*beta)+1).
```

For `0 <= beta < log 3 / 16`, `q(beta) < 1` without a volume factor.

For physical left geometry, a spatial link has at most `18` distinct intrinsic spatial plaquette-neighbors. Adding the resampled fiber and distinguished right target produces a C5 exceptional set of size at most `20`.

This proves bounded bare/local interaction degree. It does **not** by itself prove decay of the nonlocal ground-state contribution.

---

# Phase 4 — Physical multi-step restricted scan

**Status: Integrated.**

The physical lane contains

```text
same-fiber two-step propagation
-> distinct-fiber transport
-> arbitrary deterministic schedules
-> generic restricted-target random scan
-> actual continuous C5 restricted random scan
-> measurable one-step affine transport
-> finite-step expectation iterate
-> tagged variation domination.
```

Only `Sum.inl` physical fibers are scanned. `Sum.inr` source coordinates remain static parameters.

The older all-links off-fiber Harnack coefficient remains a valid dense majorant. It is retained as an obstruction/baseline theorem, not as the sharp description of direct Wilson geometry.

---

# Phase 5 — Remote defect localization and fixed-right probability law

**Status: Integrated.**

Outside the exceptional set, a background source is distinct from the resampled fiber, distinct from the distinguished target, and shares no spatial Wilson plaquette with the relevant local interaction.

Under those literal geometric hypotheses:

```text
target-local-factor contribution cancels exactly;
raw one-slab four-point contribution cancels exactly;
remaining full C5 defect is the ground-state/vacuum defect.
```

The remaining weighted covariance is rewritten using

```text
w_C(A) = Omega(A) * K(A,C).
```

The formalization proves enough positivity/integrability to define

```text
nu_C = w_C dmu / Z_C,
Z_C > 0,
```

and obtains the exact normalization identity

```text
WeightedCovarianceNumerator(w_C; f,g)
  = Z_C^2 * Cov_{nu_C}(f,g).
```

No RCD/Gibbs interpretation is required for this result.

---

# Phase 6 — Exact fixed-right source-response chain

**Status: Integrated through #4355.**

This phase converts the probability covariance from Phase 5 into a source-response problem that can be acted on by the physical scan.

The sequence is:

```text
#4337
  one-link vacuum right-boundary ratio
  = expectation of a literal target-local factor under nu_C

#4339
  changing one right-boundary link
  = normalized local tilt
  -> exact covariance response for arbitrary real observables

#4342
  two-source kernel-section response
  = crossing covariance / crossing mean

#4345
  specialize the arbitrary observable to the literal target-local ratio

#4348
  identify the remote full reference probability law exactly with the
  fixed-right kernel-section law at the source-then-target updated boundary

#4353
  remote C5 covariance
  = positive crossing mean * fixed-right target response
  with the pre-existing physical factors retained explicitly

#4355
  insert that exact response into the exceptional-set remote residual lane.
```

The important boundary is that these are exact identities and rewrites. They do not yet provide decay or summability.

---

# Phase 7 — Stationary restricted-C5 finite-step response

**Status: Integrated through #4367.**

This is the major change since the previous ROADMAP.

## 7.1 Exact stationarity

PR #4360 proves the required stationarity of the normalized continuous-vacuum reference law under the physical restricted C5 heat-bath dynamics and lifts it through schedule/random-scan iteration.

## 7.2 Generic finite-step response residual

PR #4363 proves the actual finite-step recursion of the form

```text
stationary response
<= accumulated tagged source forcing
 + terminal response after n scans.
```

This is the physical `R <= D + Q R` iteration interface, not merely an abstract comparison statement.

## 7.3 Literal target-ratio specialization

PR #4367 takes

```text
F_target(A)
  = localFactor(A,target,g1) / localFactor(A,target,g2)
```

and proves:

```text
F_target > 0;
F_target <= exp(16*beta);
F_target is strongly measurable;
F_target is integrable under every relevant probability law.
```

Its coordinate variation is bounded by the singleton profile

```text
variation_target(e)
  = exp(16*beta) if e = target
    0            otherwise.
```

For a remote target/source pair, the exact fixed-right source response therefore satisfies schematically

```text
|E_{nu_h} F_target - E_{nu_k} F_target|
<= TaggedVariationIterate(variation_target, n, Sum.inr source)
 + |E_{nu_h}(Q_k^n F_target) - E_{nu_k}(Q_k^n F_target)|.
```

Here the notation is schematic: the Lean theorem uses the concrete restricted-random-scan expectation iterate and exact source/target-updated kernel-section probability laws.

This removes the earlier need to assign a volume-wide initial variation to the target-ratio observable.

---

# Phase 8 — Volume-independent exceptional-plus-residual interface

**Status: Integrated interface.**

The already-proved geometry gives the abstract column estimate

```text
influence(target,source)
  <= exceptionalContribution(target,source)
     + residual(target,source),
```

with at most `20` exceptional targets per source. Hence

```text
sum_target influence(target,source)
  <= 20 * eta + sum_target residual(target,source).
```

If

```text
sup_source sum_target residual(target,source) <= rho,
```

then

```text
columnSum <= 20 * eta + rho.
```

Thus

```text
20 * eta + rho < 1
```

is a sufficient volume-independent strict-contraction gate.

The interface is complete. The concrete continuous-SU(N) `rho` remains open.

---

# Phase 9 — Close the #4367 residual

**Status: OPEN NOW.**

The exact remaining quantity has two pieces:

```text
A. tagged restricted-scan propagation from the singleton target variation;
B. terminal response of the common k-smoothed target-ratio observable.
```

The next theorem must control these terms in a way that is remote-column summable uniformly in periodic volume.

A valid route must avoid the circular implication

```text
assume global C5 contraction
-> prove terminal response decay
-> use terminal response decay to prove global C5 contraction.
```

Possible proof interfaces already present in the repository include finite-step transport, response/certificate algebra, sweep/resolvent machinery, and transfer/conditional-expectation structures. They may be used only through hypotheses that are already independently established for the continuous physical model.

The target output is schematically

```text
fixedRightResponse(target,source)
<= responseResidual(target,source)
```

with

```text
sup_source
  sum_{remote target} responseResidual(target,source)
<= rho_response
```

uniformly in volume.

A uniform pointwise constant followed by summation over all remote targets is not sufficient if it recreates `card Link`.

---

# Phase 10 — Convert response closure to the physical remote residual

**Status: OPEN NEXT.**

Once Phase 9 supplies a summable fixed-right response profile, transport it back through the exact #4353/#4355 identities while retaining the explicit source spatial factor, kernel-section mass factors, and crossing mean.

The goal is a genuine physical residual bound

```text
sup_source
  sum_{remote target}
    physicalResidual(target,source)
<= rho
```

with `rho` independent of periodic volume.

Then combine with Phase 8:

```text
column <= 20 * eta + rho.
```

The first decisive continuous-SU(N) contraction milestone is a proved parameter regime satisfying

```text
20 * eta + rho < 1.
```

Until that inequality is established with concrete physical witnesses, the repository should not describe the continuous physical C5 lane as globally contractive.

---

# Phase 11 — Actual continuous response certificate and resolvent/sweep closure

**Status: OPEN NEXT.**

After a strict physical column bound is available:

```text
physical source discrepancy
+ concrete sourceBound / residual witnesses
+ strict column control
-> instantiate the existing response certificate
-> source resolvent
-> sweep comparison
-> quantitative response closure.
```

The generic algebra is not the current obstruction. The obstruction is supplying the continuous physical witnesses without circularity and without a volume-growing bound.

---

# Phase 12 — Physical Poincare/coercivity

**Status: OPEN DOWNSTREAM.**

The intended route is

```text
continuous physical response control
-> block/conditional variance estimate
-> quantitative Poincare/coercivity inequality
-> uniform control on the physical transfer sector.
```

This phase must use the actual physical continuous witnesses, not Z2-specific decay theorems or abstract coefficients that have not been instantiated for `SU(N)`.

---

# Phase 13 — Uniform finite-volume transfer gap

**Status: OPEN DOWNSTREAM.**

The required target is a scale-independent positive constant

```text
kappa_* > 0
```

feeding the physical transfer/Hamiltonian route uniformly over the finite periodic volumes used in the limiting construction.

A finite-volume gap theorem whose constant collapses with volume is insufficient for the final program.

---

# Phase 14 — Thermodynamic/continuum physical limit

**Status: OPEN DOWNSTREAM.**

After a uniform finite-volume physical gap is established, the remaining program includes:

```text
tight/compatible limiting physical states
-> same-root OS/Wightman carrier
-> limiting semigroup/Hamiltonian
-> nontrivial sufficiently rich 4D Yang--Mills field/state
-> spectral lower bound above vacuum.
```

The already-integrated scalar continuum OS lane is infrastructure and evidence of a same-root continuum construction pattern; it is not by itself the complete Yang--Mills field/state required here.

---

# Phase 15 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete construction meeting the Yang--Mills existence and mass-gap requirements in the intended four-dimensional setting.

The present repository contains a large formal finite/continuous proof spine and increasingly concrete quantitative physical interfaces, but it deliberately keeps the final claim boundary open until every finite-volume, uniformity, limiting, field-content, and spectral obligation is discharged.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline #4367:

```text
1. Inspect the exact tagged variation iterate generated by
   variation_target = exp(16*beta) * 1_{target}.

2. Derive the strongest available non-circular estimate for its transport
   from target to represented source under the actual restricted scan.

3. Analyze the terminal term
   |E_{nu_h}(Q_k^n F_target) - E_{nu_k}(Q_k^n F_target)|
   using only independently established stationarity/transfer structure.

4. Choose/optimize n only after the two estimates are explicit; do not hide
   a volume-dependent choice in the notation.

5. Package the result as a geometry-sensitive remote response profile.

6. Prove uniform remote-column summability of that profile.

7. Push it through #4353/#4355 to obtain the concrete physical rho.

8. Combine with the exceptional contribution 20*eta.

9. Establish, if possible, a concrete parameter regime
   20*eta + rho < 1.

10. Instantiate the existing response certificate/resolvent/sweep route and
    continue toward physical Poincare/coercivity.
```

The conceptual transition is therefore:

```text
#4270 frontier:
  remote defect identified as a fixed-right probability covariance

#4367 frontier:
  that covariance has been converted to an exact physical stationary
  finite-step response residual with singleton initial variation

next frontier:
  prove that exact residual is uniformly summable in volume.
```
