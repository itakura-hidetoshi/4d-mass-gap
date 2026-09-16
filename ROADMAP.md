# MGAP4D Roadmap

This roadmap records the theorem architecture and development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-16 JST**.

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest theorem-bearing canonical merge at the time of this documentation update is

```text
5c392b82ef522006885740ad85588a792d340a2a
```

with tree

```text
75bc12fa5f2e2dae613e3f051a89fff470522310.
```

This is the merge of PR #4270,

```text
Sharpen C5 distinct-background Harnack off target
```

from exact GREEN proof head

```text
236e9d0e31b88c7ca103915ea8dd38b0e5e41f21
```

validated by

```text
PR Lean Fast Check #13994
workflow run 35086312903
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
> The physical restricted random scan, finite-step transport, and geometric forcing residual are already integrated. PR #4270 changes the interpretation of the remaining left-left problem: the old coefficient
>
> ```text
> (card Link - 1) * offFiberInfluence(beta)
> ```
>
> remains a correct dense majorant, but it no longer describes the sharp local Wilson geometry. Direct spatial Wilson interaction has degree at most `18`; after adding the resampled fiber and distinguished right target, the C5 exceptional background set has cardinality at most `20`. Outside that set, all local Wilson four-point distortion cancels and the remaining defect is exactly a probability covariance under a normalized fixed-right ground-state kernel-section law.
>
> The immediate open problem is therefore to prove a **volume-independent summable bound on that remote probability-covariance residual**. The abstract C5 contraction gate
>
> ```text
> column <= 20 * eta + rho
> ```
>
> is already formalized; the concrete physical `rho` is not.

---

## Status legend

- **Integrated** — merged theorem/model result on the authoritative branch.
- **Integrated routing** — implication chain is formalized, but a quantitative physical input remains open.
- **Integrated interface** — theorem is proved, but concrete physical witnesses remain to be supplied.
- **Obstruction integrated** — a tempting route has been exposed as insufficient or semantically invalid.
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
  -> spatial conditional-expectation projections
  -> block Poincare/coercivity routing
  -> physical transfer-gap route

D. SHARP CONTINUOUS ONE-LINK CONTROL                           [INTEGRATED]

continuous-vacuum one-link law
  -> Harnack / normalized comparison
  -> one-link variance lower bound
  -> physical one-link Doob bridge

E. RIGHT-BOUNDARY C5 EXACT LOCALITY                            [INTEGRATED]

right source != resampled fiber
  -> scalar multiple of common weight
  -> normalization cancellation
  -> normalized laws / kernels equal
  -> represented influence exactly zero

right source = resampled fiber
  -> q(beta) = 2*(exp(16 beta)-1)/(exp(16 beta)+1)
  -> beta < log 3/16 => q(beta) < 1

F. ONE-WAY TAGGED CARRIER + RESPONSE ALGEBRA                   [INTEGRATED]

Sum.inl target <- Sum.inr source
  -> represented C5 coefficient
  -> source-resolvent / sweep machinery
  -> state-space-independent response certificate interface

G. ACTUAL PHYSICAL TWO-STEP TRANSPORT                          [INTEGRATED]

#4217 same-fiber propagation
#4220 explicit left-left carrier
#4223 distinct-fiber continuous C5 comparison
#4237 assumption-free two-step transport

H. DETERMINISTIC / RESTRICTED RANDOM SCAN                      [INTEGRATED]

#4242 deterministic schedules
#4249 generic restricted-target scan
#4252 actual continuous C5 restricted scan
#4254 one-step measurable affine transport
#4257 finite-step physical expectation iterate

Only Sum.inl physical fibers are scanned.
Sum.inr source coordinates remain static parameters.

I. RESTRICTED GEOMETRIC FORCING RESIDUAL                       [INTEGRATED]

#4260 generic restricted-target residual
#4266 physical C5 specialization
  -> exact dense-majorant left column coefficient
     (card Link - 1) * offFiberInfluence(beta)
  -> finite-step physical boundary-response residual

J. LOCAL C5 GEOMETRY SHARPENING                                [INTEGRATED]

#4270 off-target local-factor invariance
  -> raw off-target Harnack exp(32 beta) -> exp(16 beta)
  -> active-neighbor degree <= 18
  -> C5 exceptional set <= 20

K. REMOTE WILSON CANCELLATION                                  [INTEGRATED]

outside exceptional set:
  target-local factor cancels
  + raw slab four-point defect cancels
  -> full C5 defect = canonical vacuum defect
  -> weighted covariance normal form

L. GROUND-STATE KERNEL-SECTION PROBABILITY                     [INTEGRATED]

w_C(A) = Omega_eig(A) * K(A,C)
  -> exact kernel-section form
  -> integrable / a.e. nonnegative
  -> mass Z_C = ||T|| * Omega_cont(C) > 0
  -> normalized probability nu_C
  -> WeightedCovNum = Z_C^2 * Cov_{nu_C}

outside exceptional set:
  remote C5 defect
  = sourceSpatialRatio * Z_C^2 * probability covariance

M. VOLUME-INDEPENDENT C5 COLUMN GATE                           [INTEGRATED INTERFACE]

exceptional contribution <= 20 * eta
remote residual column <= rho
  -> column <= 20 * eta + rho
  -> 20 * eta + rho < 1 => strict contraction

N. SUMMABLE GROUND-STATE COVARIANCE RESIDUAL                   [OPEN NOW]

prove a concrete continuous-SU(N) bound
  sup_source sum_remote residual(target,source) <= rho
with rho independent of periodic volume

O. ACTUAL CONTINUOUS RESPONSE CERTIFICATE                      [OPEN NEXT]

uniform physical residual
  + concrete discrepancy/sourceBound witnesses
  -> instantiate response certificate
  -> reuse source-resolvent / sweep machinery

P. PHYSICAL POINCARE / COERCIVITY                              [OPEN DOWNSTREAM]

physical response control
  -> quantitative block coercivity
  -> spatial conditional inequalities

Q. UNIFORM FINITE-VOLUME TRANSFER GAP                          [OPEN DOWNSTREAM]

scale-independent kappa_* > 0
  -> physical transfer-gap lower bound

R. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                    [OPEN DOWNSTREAM]

uniform finite-volume gap
  -> limiting physical carrier
  -> OS/Wightman spectral lower bound
  -> sufficiently rich same-root 4D Yang--Mills field/state

S. CLAY-LEVEL EXISTENCE + MASS GAP                             [OPEN]
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
-> inspect actual CI failures
-> apply the minimal proof-preserving fix
-> require terminal completed/success receipt
-> merge with expected_head_sha
-> fresh-fetch canonical branch again.
```

Queued or in-progress CI is not success. New `sorry`, `admit`, axioms, assumption weakening, or semantic broadening are not acceptable substitutes for proof.

Permanent distinctions include:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
right-boundary exact cancellation != arbitrary left-left cancellation
one-way carrier zero != reverse physical influence zero
Sum.inl link != Sum.inr link
full tagged random scan != physical restricted random scan
old dense Harnack majorant != actual Wilson interaction graph
bounded local degree != decay of a global ground-state covariance
probability normalization != conditional independence
finite-step transport != volume-uniform contraction
uniform finite-volume gap != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion.
```

---

# Phase 1 — Finite Wilson root and OS infrastructure

**Status: Integrated.**

The finite theorem root contains the periodic-even compact `SU(N)` Wilson Gibbs construction, lattice geometry, normalized Haar reference measure, Wilson action, reflection positivity, gauge-covariant structures, spatial-slice carriers, one-slab transfer operators, and positive ground-state architecture.

The route from spatial conditional estimates to a finite-volume physical transfer gap is formalized as routing. A model-derived volume-uniform quantitative coefficient remains a downstream obligation.

---

# Phase 2 — Same-root scalar continuum OS lane

**Status: Integrated as a scalar observable lane.**

The repository constructs a continuum scalar law from finite Wilson readouts, establishes continuum reflection positivity, forms an OS Hilbert carrier, and obtains a real strongly continuous contraction semigroup with self-adjoint Hamiltonian and vacuum structure.

Boundary: this is a same-root scalar continuum lane, not yet the complete four-dimensional Yang--Mills gauge field/state required by the Clay problem.

---

# Phase 3 — Right-boundary C5 normalized locality

**Status: Integrated.**

For the literal C5 reference one-link law, changing a represented right-boundary source distinct from the resampled fiber changes the unnormalized density only by a positive scalar independent of the fiber integration variable. The scalar cancels after normalization.

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

For `0 <= beta < log 3 / 16`, `q(beta) < 1` with no volume factor.

This right-boundary theorem is not a left-left cancellation theorem.

---

# Phase 4 — Physical multi-step bridge

**Status: Integrated through #4266.**

The physical lane now contains:

```text
same-fiber two-step propagation
-> distinct-fiber transport
-> arbitrary deterministic schedules
-> actual restricted random scan
-> finite-step expectation iterate
-> tagged variation domination
-> physical finite-step boundary-response residual.
```

The older distinct-fiber Harnack route supplied the uniform off-fiber coefficient

```text
offFiberInfluence(beta)
  = 2 * (((exp(32*beta))^2 - 1)
         / ((exp(32*beta))^2 + 1)).
```

and #4266 computed the corresponding dense-majorant column coefficient

```text
(card Link - 1) * offFiberInfluence(beta).
```

That theorem remains correct. Its interpretation is now sharpened by #4270: it is a bound obtained by assigning the same off-fiber coefficient to every distinct link, not a theorem that every distinct pair has direct Wilson interaction.

---

# Phase 5 — Bounded local geometry

**Status: Integrated by #4270.**

The target-local factor depends on the relevant background only through the target coordinate. Therefore an update at a distinct background fiber leaves that factor exactly unchanged, reducing the raw off-target Harnack cost from

```text
exp(32 * beta)
```

to

```text
exp(16 * beta).
```

Separately, the intrinsic spatial Wilson geometry is counted exactly enough to prove

```text
card activeNeighbors(fiber) <= 18.
```

The C5 exceptional background set is then

```text
insert fiber (insert distinguishedTarget activeNeighbors(fiber))
```

with

```text
card exceptional <= 20
```

uniformly in periodic volume.

This establishes bounded **bare/local** interaction degree. It does not establish decay of the global vacuum contribution.

---

# Phase 6 — Remote C5 four-point cancellation

**Status: Integrated by #4270.**

Outside the exceptional set, a background fiber is distinct from the resampled fiber, distinct from the distinguished target, and shares no spatial Wilson plaquette with the resampled fiber.

Under these literal geometric conditions:

```text
target-local factor contribution cancels exactly;
raw one-slab four-point contribution cancels exactly;
full C5 reference-weight defect reduces to the vacuum defect.
```

The remaining vacuum defect is then localized as a weighted covariance numerator of two one-link observables:

```text
target observable:
  ratio of target-local factors;

source observable:
  ratio of one-link Wilson crossing kernels.
```

No distance decay is asserted at this stage.

---

# Phase 7 — Fixed-right ground-state kernel-section probability

**Status: Integrated by #4270.**

The covariance weight is exactly rewritten as

```text
w_C(A)
  = Omega_eig(A) * K(A,C),
```

where `C` is the doubly updated right boundary.

The formalization proves:

```text
w_C is integrable;
w_C >= 0 almost everywhere;
Z_C = integral w_C dmu
    = ||T|| * Omega_cont(C) > 0.
```

Thus

```text
nu_C = w_C dmu / Z_C
```

is a genuine probability measure.

The generic weighted normalization identity then gives

```text
WeightedCovarianceNumerator(w_C; f,g)
  = Z_C^2 * Cov_{nu_C}(f,g).
```

Finally, outside the C5 exceptional set, the literal remote four-point defect is exactly

```text
sourceSpatialRatio
* Z_C^2
* Cov_{nu_C}(targetLocalRatio, sourceCrossingRatio).
```

This result deliberately stops short of identifying `nu_C` with a regular conditional probability. No such identification is needed for the covariance normal form.

---

# Phase 8 — Volume-independent exceptional-plus-residual gate

**Status: Integrated interface.**

For any influence/residual pair satisfying the pointwise decomposition

```text
influence(target,source)
  <= (if target in exceptional(source) then eta else 0)
     + residual(target,source),
```

one has

```text
sum_target influence(target,source)
  <= 20 * eta
     + sum_target residual(target,source).
```

If

```text
sum_target residual(target,source) <= rho
```

uniformly in source, then

```text
columnSum <= 20 * eta + rho.
```

Therefore

```text
20 * eta + rho < 1
```

is a sufficient volume-independent strict-contraction gate.

This theorem is already available. The missing task is to produce a concrete physical `residual` and a volume-independent `rho` from the continuous ground-state covariance structure.

---

# Phase 9 — Summable ground-state probability covariance

**Status: OPEN NOW.**

This is the immediate theorem-development frontier after #4270.

The required result is schematically

```text
sup_source
  sum_{remote target}
    residualOmega(target,source)
<= rho
```

with `rho` independent of the periodic spatial volume.

A uniform pointwise covariance bound followed by a sum over all remote links is **not** enough; that would simply reconstruct a cardinality factor.

Preferred theorem-development route:

```text
1. use the canonical continuous vacuum representative and its
   a.e. equality with the existing top-eigenvector L2 class;

2. express the fixed-right kernel-section probability density using
   this continuous positive representative where useful;

3. connect one-link conditionals/responses to the already-formalized
   continuous-vacuum Doob / Wilson one-link machinery;

4. derive a geometry-sensitive covariance or resolvent profile without
   assuming the global C5 contraction being proved;

5. sum that profile with the existing finite Dobrushin/resolvent
   geometric-support machinery;

6. obtain a volume-independent residual-column bound rho.
```

Circularity is forbidden: the same global contraction cannot be assumed in order to prove its own covariance decay.

Z2-specific covariance-decay lanes remain useful as structural references only. They do not prove the continuous `SU(N)` estimate.

---

# Phase 10 — Instantiate the actual continuous response certificate

**Status: OPEN NEXT.**

Once a concrete volume-independent residual column is proved, combine it with the exceptional-set bound:

```text
column <= 20 * eta + rho.
```

If the resulting coefficient is strictly below one, package the actual physical discrepancy and source-bound witnesses into the existing state-space-independent response certificate and re-enter the already-integrated source-resolvent / sweep algebra.

No new generic response architecture should be introduced unless the existing interface is genuinely insufficient.

---

# Phase 11 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

The intended route remains

```text
uniform physical response control
-> spatial block coercivity
-> quantitative conditional inequalities
-> physical Poincare/coercivity theorem.
```

This phase requires the concrete continuous physical witnesses from Phase 10.

---

# Phase 12 — Uniform finite-volume transfer gap

**Status: OPEN DOWNSTREAM.**

A scale-independent coercive coefficient must produce a uniform finite-volume physical transfer-gap lower bound.

A fixed-volume gap or finite-step contraction is not sufficient.

---

# Phase 13 — Thermodynamic / continuum physical carrier

**Status: OPEN DOWNSTREAM.**

Required tasks include stability of the physical carrier under increasing volume/scaling, preservation of the relevant OS/Wightman structures, and transport of the spectral lower bound into a sufficiently rich continuum four-dimensional Yang--Mills field/state.

The existing same-root scalar continuum construction is an important formal lane but is not by itself the complete gauge-field construction.

---

# Phase 14 — Clay-level Yang--Mills existence and mass gap

**Status: OPEN.**

The final target requires all earlier finite-volume, uniformity, limiting, field-richness, spectral, and existence obligations to be closed without changing the mathematical problem.

No intermediate Lean theorem, repository routing result, or exact finite-volume coefficient should be described as completion of the Clay problem.

---

# Immediate next theorem unit

Starting from theorem-bearing merge

```text
5c392b82ef522006885740ad85588a792d340a2a
```

the next coherent unit should stay close to the actual continuous kernel-section probability law rather than adding another generic abstraction.

Preferred target:

```text
construct an exact one-link conditional/response bridge for nu_C
using the canonical continuous vacuum representative,
then expose the remote covariance to the existing Dobrushin/resolvent
geometric-support machinery.
```

The success criterion for that unit is **not** yet the mass gap. It is a theorem that turns the currently exact probability-covariance localization into a quantitatively summable, volume-independent residual estimate without circular assumptions.
