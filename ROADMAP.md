# MGAP4D Roadmap

This roadmap records the current proof architecture and theorem-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-15 JST**.

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest theorem-bearing merge before this documentation refresh is

```text
a05876f44f1bf387ad070889de6487bd37b2121b
```

with tree

```text
2751d346ef5149f1e31848eeb5089c8d1ceb9061
```

This is the merge of PR #4211,

```text
Lift continuous C5 heat-bath variation to row operator
```

from exact GREEN head

```text
3e570acaacd62d1ce50c1558587d7b6d53917a07
```

validated by

```text
PR Lean Fast Check #13919
workflow run 34961303873
workflow / job / changed-Lean step: completed / success
```

`main` is a public landing surface, not theorem authority. The authority order remains:

```text
exact canonical SHA
-> formal Lean artifacts
-> README / ROADMAP
-> CI/runtime receipts
-> historical summaries or memory.
```

> **Current frontier**
>
> The C5 local continuous-state influence problem has advanced through the full represented right-source **one-link variation row**. The remaining obstruction is now multi-step: prove that actual continuous C5 update compositions carry variation profiles through a recurrence dominated by the existing tagged kernel update/iterate, without silently identifying the generic `Sum Link Link` random scan with a physical continuous random-scan process.
>
> Once that descent is proved, the next target is the actual continuous finite-step kernel residual. That residual can be packaged by the already-merged state-space-independent certificate constructor and fed directly into the already-proved source-resolvent / sweep-scaled response algebra.

---

## Status legend

- **Integrated** — merged theorem/model result on the authoritative branch.
- **Integrated routing** — implication chain is formalized but a quantitative physical/model input remains open.
- **Integrated conditional interface** — theorem is proved, but concrete witnesses must be supplied separately.
- **Obstruction integrated** — a tempting route has been formally shown insufficient or semantically invalid.
- **Open now** — immediate theorem-development frontier.
- **Open next** — next coherent unit after the present frontier.
- **Open downstream** — required later in the global mass-gap route.

---

# Roadmap in one view

```text
A. FINITE WILSON / OS ROOT                                      [Integrated]

periodic-even compact SU(N) Wilson model
  -> reflection geometry / OS positivity
  -> spatial-slice and boundary L2 carriers
  -> physical one-slab transfer / ground-state structure

B. SAME-ROOT SCALAR CONTINUUM OS                               [Integrated]

finite Wilson scalar readout
  -> same-root continuum scalar probability law
  -> continuum reflection positivity
  -> OS Hilbert carrier / C0 semigroup / Hamiltonian

C. FINITE PHYSICAL CONDITIONAL / GAP ROUTING                   [Integrated routing]

ground-state joint law
  -> six-right + six-left genuine spatial condExp projections
  -> twelve-spatial family
  -> Poincare/coercivity -> physical transfer-gap route

D. SHARP CONTINUOUS ONE-LINK CONTROL                           [Integrated]

continuous-vacuum one-link weight
  -> Harnack / normalized comparison
  -> one-link variance lower bound
  -> bounded-core conditional residual

E. CONSTANT REMOTE-BOUND ROUTE                                [Obstruction integrated]

nonzero constant remote coefficient
  -> source-cardinality loss
  -> no volume-independent row contraction from that route alone

F. C5 LOCALITY / NORMALIZED DISTINCT-SOURCE INVARIANCE         [Integrated]

source-local factorization
  -> source != fiber gives scalar multiple of common weight
  -> scalar cancels after normalization
  -> normalized fiber laws equal
  -> conditional kernels equal
  -> heat-bath kernels equal
  -> real-test influence exactly zero

G. C5 DIAGONAL SUPPORT / COEFFICIENT                           [Integrated]

only source = fiber survives
  -> q(beta) = 2*(exp(16 beta)-1)/(exp(16 beta)+1)
  -> row sum = q(beta)
  -> beta < log 3/16 => 0 <= q(beta) < 1

H. ONE-WAY TAGGED CARRIER                                      [Integrated]

ι_H = Sum Link Link
Sum.inl target <- Sum.inr source = proved C5 influence
all other blocks = carrier-scope zero only
  -> row / right-source-column coefficient q(beta)

I. GENERIC RANDOM-SCAN / RESOLVENT ALGEBRA                     [Integrated]

r_{H,beta} = 1 - (1-q(beta))/|ι_H|
  -> finite kernel variation iteration
  -> source partial sums / resolvent
  -> sweep scaling
     r^{|ι_H| s} <= exp(-(1-q)s)

J. STATE-SPACE-INDEPENDENT RESPONSE CERTIFICATE                [Integrated interface]

FiniteKernelStationaryResponseFamilyCertificate
  -> no finite local state required downstream
  -> #4192 response algebra
  -> #4198 raw continuous-witness constructor

K. ACTUAL CONTINUOUS SU(N) VARIATION REALIZATION               [Integrated through #4211]

actual one-link bounded-test influence
  -> fiber-variation scaling                              #4201
  -> tagged-kernel entry                                 #4205
  -> one generic target-update domination                #4208
  -> full represented right-source row
     <= physical influence operator                      #4211

L. PHYSICAL MULTI-STEP VARIATION PROPAGATION                  [OPEN NOW]

actual continuous update sequence
  -> one-step profile recurrence for every relevant step
  -> composition / induction
  -> domination by an appropriate generic tagged iterate

M. CONTINUOUS FINITE-STEP KERNEL RESIDUAL                     [OPEN NEXT]

multi-step variation domination
+ genuine source-bound witness
  -> discrepancy <= partialSource + 2 * terminalVariation

N. ACTUAL CONTINUOUS RESPONSE CERTIFICATE                     [OPEN NEXT]

continuous residual witnesses
  -> #4198 constructor
  -> FiniteKernelStationaryResponseFamilyCertificate

O. SOURCE-SUMMED / SWEEP-SCALED PHYSICAL RESPONSE             [OPEN AFTER N]

actual certificate
  -> existing #4192 resolvent/geometric residual
  -> existing normalized source/sweep algebra

P. PHYSICAL POINCARE / COERCIVITY BRIDGE                      [OPEN DOWNSTREAM]

physical response control
  -> same-color / relevant block coercivity
  -> six-right + six-left block control
  -> quantitative twelve-spatial coefficient

Q. UNIFORM FINITE-VOLUME GAP                                  [OPEN DOWNSTREAM]

scale-independent kappa_* > 0
  -> physical transfer gap >= 3 kappa_*/4

R. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                   [OPEN DOWNSTREAM]

uniform finite-volume physical gap
  -> limiting physical carrier
  -> OS/Wightman spectral lower bound
  -> sufficiently rich same-root 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
```

---

# Phase 0 — Authority and proof discipline

**Status: Integrated and permanent.**

For theorem-bearing work:

```text
fresh-fetch authoritative branch
-> start from exact canonical SHA
-> inspect exact existing theorem interfaces
-> RED theorem / Draft PR
-> wait for terminal failed CI
-> inspect actual Lean failure
-> minimal GREEN patch
-> wait for terminal successful workflow/job/Lean step
-> record GREEN SHA and run receipt
-> Ready
-> merge with expected_head_sha
-> fresh-fetch canonical branch again
```

Queued, pending, or in-progress CI is not success. Repository operations are GitHub-mediated. New `sorry`, `admit`, axioms, assumption weakening, or semantic broadening of a theorem are not acceptable substitutes for proof.

Permanent distinctions:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
covariance localization != spatial decay
C5 raw one-slab law != full-4D Wilson singleLinkConditionalMeasure
C5 exact distinct-source invariance != arbitrary full-4D remote invariance
one-way tagged zero block != reverse physical influence zero
Sum.inl link != Sum.inr link
generic tagged random scan != physical continuous random scan by definition
finite positive-weight comparison != continuous SU(N) comparison
state-space-independent certificate interface != existence of physical witnesses
stationary response bound != physical coercivity theorem
finite-volume contraction != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion
```

---

# Phase 1 — Finite Wilson root and OS infrastructure

**Status: Integrated.**

The finite theorem root contains the periodic-even compact `SU(N)` Wilson Gibbs construction, lattice geometry, normalized Haar reference measure, Wilson action, reflection positivity, gauge-covariant structures, spatial-slice carriers, one-slab transfer operators, and positive ground-state architecture.

The route from spatial conditional estimates to a finite-volume physical transfer gap is already formalized as routing. What remains downstream is a model-derived quantitative coefficient with the required volume/scale behavior.

---

# Phase 2 — Same-root scalar continuum OS lane

**Status: Integrated as a scalar observable lane.**

The repository constructs a continuum scalar law from finite Wilson readouts, establishes continuum reflection positivity, forms an OS Hilbert carrier, and obtains a real strongly continuous contraction semigroup with self-adjoint Hamiltonian and vacuum structure.

Boundary: this is a same-root scalar continuum lane, not yet the complete four-dimensional Yang--Mills gauge field/state required by the Clay problem.

---

# Phase 3 — Sharp one-link control and the failed constant-remote route

**Status: Integrated / obstruction integrated.**

The continuous-vacuum one-link law has volume-independent local Harnack and variance control. However, summing a nonzero constant influence coefficient over all remote sources produces an explicit source-cardinality loss. The repository records this as a permanent obstruction rather than hiding it behind a nominal contraction statement.

The successful C5 route therefore uses exact normalized cancellation, not an assumed spatial exponential decay.

---

# Phase 4 — C5 normalized distinct-source invariance

**Status: Integrated.**

For the literal C5 reference one-link law, when

```text
source != fiber,
```

the source-sensitive unnormalized weight factors as

```text
W_k(g) = c_k * W_base(g)
```

with `c_k > 0` independent of the fiber variable `g`. The same scalar multiplies the partition function, hence cancels from the normalized probability measure.

Consequences already merged:

```text
normalized fiber law equality
-> conditional-kernel equality
-> heat-bath-kernel equality
-> exact zero real-test source influence.
```

This is stronger than a decaying estimate on this specific carrier, but it does not assert arbitrary full-4D remote invariance.

---

# Phase 5 — Surviving diagonal influence

**Status: Integrated.**

At `source = fiber`, the sharp comparison gives

```text
q(beta)
  = 2 * (((exp (8*beta))^2 - 1)
          / ((exp (8*beta))^2 + 1))
  = 2 * (exp(16*beta)-1)/(exp(16*beta)+1).
```

All other represented sources vanish exactly, so the full source row is supported at one coordinate:

```text
rowSum = q(beta).
```

For

```text
0 <= beta < log 3 / 16,
```

one has

```text
0 <= q(beta) < 1.
```

No volume factor and no unproved `C * exp(-m*d)` estimate is used.

---

# Phase 6 — One-way tagged carrier and generic kernel algebra

**Status: Integrated.**

The proved cross-boundary direction is represented on

```text
ι_H = Sum Link Link
```

with left targets in `Sum.inl` and right sources in `Sum.inr`.

Only the right-source to left-target block carries the proved coefficient. The other blocks are zero because the carrier is intentionally one-way. The zeros have no independent reverse-physical meaning.

The generic kernel layer provides

```text
finiteInfluenceKernelUpdatedVariation
finiteInfluenceKernelRandomScanUpdatedVariation
finiteInfluenceKernelRandomScanVariationIterate
finiteInfluenceKernelPartialSource
```

plus positivity, monotonicity, scaling, column contraction, and source-resolvent identities.

The reciprocal one-coordinate rate is

```text
r_{H,beta} = 1 - (1-q(beta))/|ι_H|.
```

It is finite-volume contractive but not uniformly separated from one. Full tagged sweeps satisfy

```text
r_{H,beta}^{|ι_H| * sweeps}
  <= exp(-(1-q(beta))*sweeps),
```

which is the correct volume-independent time scaling.

---

# Phase 7 — Finite comparison lane and source averaging

**Status: Integrated conditional realization.**

The finite positive-weight stationary non-strict comparison lane remains a fully proved realization of the generic kernel algebra. Source resolvent and source averaging have been sharpened through the #4165–#4190 sequence, including:

```text
source-resolvent cardinality cancellation
source-summed expectation-discrepancy control
source-average normalization
sweep-scaled terminal residual
local-tilt source-average realization (#4187)
pointwise stationary source-bound route (#4190).
```

These theorems establish the algebra and one finite realization. They do **not** turn the actual continuous C5 law into a finite-state model.

---

# Phase 8 — State-space-independent certificate

**Status: Integrated interface through #4192 and #4198.**

PR #4192 introduces

```text
FiniteKernelStationaryResponseFamilyCertificate
```

whose essential data are:

```text
discrepancy
sourceBound
sourceBound_nonneg
variation
variation_nonneg
discrepancy_le_kernelResidual.
```

The downstream C5 kernel/resolvent algebra depends on this certificate rather than on a finite local state space.

PR #4198 adds

```text
...kernelResponseCertificateOfResidual
```

and a direct raw-witness entry point into the source-summed resolvent theorem.

Boundary: #4198 packages witnesses; it does not construct the physical continuous witnesses.

---

# Phase 9 — Actual continuous fiber-variation bound

**Status: Integrated by #4201.**

The previous bounded-test normalization `|F| <= 1` has been lifted to a true fiber-oscillation radius. For a strongly measurable observable with

```text
|F(update A fiber g) - F(update A fiber h)| <= magnitude,
```

the actual continuous C5 heat-bath expectation difference under a represented right-source value change is bounded by

```text
CrossBoundaryBoundedTestMajorant beta fiber source * magnitude.
```

This is the principal physical continuous local input to the current finite-step program.

---

# Phase 10 — Transport into the one-way tagged kernel

**Status: Integrated by #4205 and #4208.**

PR #4205 rewrites the #4201 coefficient as the actual represented tagged-kernel entry

```text
K.influence (Sum.inl fiber) (Sum.inr source).
```

PR #4208 defines the left-only bookkeeping lift

```text
leftVariation (Sum.inl fiber) = variation fiber
leftVariation (Sum.inr source) = 0
```

and proves that the actual continuous one-source expectation difference is bounded by one generic

```text
finiteInfluenceKernelUpdatedVariation
```

step at the represented tagged pair.

The right-copy zero is a choice of variation representation for the observable. It is not a reverse physical-influence theorem.

---

# Phase 11 — Realize the full represented physical source row

**Status: Integrated by #4211.**

The one-source continuous theorem is now summed over all represented right-boundary source coordinates. For a fixed physical left fiber,

```text
sum_source
  |heatBathExpectation(k1 source) - heatBathExpectation(k2 source)|
```

is bounded by

```text
CrossBoundaryInfluenceOperator H beta variation fiber.
```

The proof works source-by-source. The unique diagonal source uses the #4201 fiber-variation bound; every off-diagonal source is discharged by exact support of the C5 majorant.

This closes the **one-link row realization**. It does not yet give an `n`-step physical update theorem.

---

# Phase 12 — Physical multi-step variation propagation

**Status: OPEN NOW.**

This is the immediate theorem unit after #4211.

## Required mathematical object

Represent a finite sequence of actual continuous C5 heat-bath updates, or another sufficiently precise continuous update composition, together with a physical variation profile after each step.

## Target recurrence

For each actual update at a relevant coordinate, prove a pointwise variation bound of the form

```text
physicalVariation_{m+1}
  <= appropriate generic tagged update of physicalVariation_m.
```

Then prove by induction that after `n` steps the physical profile is dominated by the corresponding generic finite-kernel iterate.

## Critical semantic obstruction

Do **not** write

```text
physical continuous random scan
  = finiteInfluenceKernelRandomScanVariationIterate K
```

without a theorem constructing that equality.

The generic random-scan operator averages targets over the full tagged index `Sum Link Link`. The current physical results describe an actual continuous heat-bath update on the represented C5 fibers. A compatibility theorem, a domination theorem, or a more precise restricted update process is required before iteration.

## Preferred development order

```text
1. define/identify one actual physical update composition;
2. prove preservation of strong measurability/integrability needed for re-use;
3. prove its fiber variation after one step;
4. match that bound to finiteInfluenceKernelUpdatedVariation;
5. compose two steps explicitly;
6. generalize by induction;
7. only then average or randomize targets if mathematically justified.
```

No new generic abstraction should be introduced unless the specialized continuous C5 proof shows it is genuinely needed.

---

# Phase 13 — Continuous finite-step kernel residual

**Status: OPEN NEXT.**

After Phase 12, prove the actual continuous residual inequality required by the certificate:

```text
discrepancy source
  <= finiteInfluenceKernelPartialSource
       K sourceEnvelope variation n
     + 2 * finiteProductVariationTotal
       (finiteInfluenceKernelRandomScanVariationIterate
         K variation n).
```

The proof must identify the actual physical meaning of `discrepancy` and `sourceBound` and show why the physical iteration is controlled by the generic terms appearing on the right.

For the source-family theorem, specialize the initial variation to the existing singleton tagged profile rather than creating a finite local state space.

---

# Phase 14 — Instantiate the actual continuous response certificate

**Status: OPEN NEXT after the residual.**

Supply to the #4198 constructor:

```text
actual continuous discrepancy
actual continuous sourceBound
sourceBound nonnegativity
actual finite-step residual theorem.
```

This produces the desired

```text
FiniteKernelStationaryResponseFamilyCertificate
```

for the actual continuous `SU(N)` comparison lane.

At this point the state-space-independent downstream machinery from #4192 can be invoked directly.

---

# Phase 15 — Re-enter the existing resolvent and sweep algebra

**Status: Algebra integrated; physical instantiation open.**

Once Phase 14 is complete, reuse the existing theorem chain rather than reproving it:

```text
continuous certificate
-> source partial response
-> source-summed resolvent
-> normalized source average
-> reciprocal random-scan terminal residual
-> sweep-scaled exponential residual.
```

The finite positive-weight comparison results provide algebraic precedent, but the actual continuous certificate must be the input.

---

# Phase 16 — Physical Poincare/coercivity bridge

**Status: Open downstream.**

The stationary/response output must then be connected to the genuine physical spatial conditional-expectation family already present in the finite Wilson/ground-state lane.

The desired direction remains

```text
physical response / variation control
  -> same-color or relevant block coercivity
  -> six-right + six-left block inequalities
  -> quantitative twelve-spatial Poincare coefficient kappa.
```

No current C5 response theorem is itself this coercivity theorem.

---

# Phase 17 — Uniform finite-volume physical transfer gap

**Status: Open downstream; routing integrated.**

The existing routing shows that a scale-independent positive twelve-spatial coefficient would feed a quantitative physical transfer-gap lower bound. The outstanding task is to obtain such a coefficient from the actual model with the required uniformity.

A positive coefficient at each fixed scale is insufficient if it degenerates along the volume/scaling sequence.

---

# Phase 18 — Thermodynamic and continuum physical propagation

**Status: Open downstream.**

A finite-volume transfer gap must still be transported through the thermodynamic/scaling limit into a limiting physical carrier. This requires explicit convergence/tightness/compatibility theorems strong enough to preserve the relevant spectral lower bound.

The already-integrated same-root scalar continuum lane is not a substitute for the complete physical four-dimensional gauge-field/state construction.

---

# Phase 19 — Clay-level endpoint

**Status: Open.**

The final endpoint still requires a sufficiently rich four-dimensional Yang--Mills field/state satisfying the relevant mathematical physics requirements together with a strictly positive spectral gap above the vacuum.

The present C5 program is an increasingly concrete finite/continuous comparison and coercivity route toward that endpoint. It must not be described as a completed Clay proof before the remaining physical finite-step, coercivity, uniformity, and continuum obligations are discharged.

---

# Immediate next theorem unit

Starting from the fresh canonical theorem-carrier SHA after this documentation refresh:

```text
1. inspect the exact #4208/#4211 one-step interfaces;
2. inspect any existing continuous kernel-composition / Markov-kernel iteration API;
3. define the narrowest actual C5 continuous update composition needed for two steps;
4. RED: state two-step variation domination;
5. GREEN: prove it from the one-step row/target-update results;
6. generalize to finite n only after the two-step semantics are sound;
7. derive the continuous finite-step kernel residual;
8. instantiate #4198's certificate constructor.
```

The intended direction is therefore

```text
one-link physical row realization
-> multi-step continuous variation propagation
-> continuous finite-step kernel residual
-> actual state-space-independent response certificate
-> existing C5 resolvent / sweep algebra
-> physical coercivity bridge.
```

That is the current mathematically coherent frontier.
