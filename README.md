# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository develops a finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer framework, exact beta-zero geometry, positive-beta response control, genuine ground-state conditional expectations, Hilbert-space sweep/coercivity machinery, and downstream thermodynamic / continuum infrastructure.

## Current status — 2026-09-27 JST

The unique authoritative theorem-carrier branch is:

**formal/real-hilbert-uniform-coercive-strong-limit**

The fresh theorem-bearing baseline immediately before this documentation refresh is:

**693c2ef8673cdfe40ec6615fc7d9c3e600dc9745**

This is the merge commit of PR **#4861**, **Charge full-direct update error to sweep path loss**.

Validated exact head of #4861:

**8f4b83ea6388b1f654fb4b67a3407c3fa6b13d68**

Validation:

- PR Lean Fast Check run **36313199617 — success**
- exact-head completion receipt **chatgpt-ci-receipt/PR Lean Fast Check — success**

The default branch **main is not theorem authority**.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> What is now integrated is substantially beyond the previous #4787 documentation snapshot. The updated-variance stationarity return is closed, the genuine target-residual reconnection is closed, the second-mean RMS feedback chain is closed, the fixed-background energy route is closed, a configuration-independent bidirectional pin-free Schur kernel is closed, the actual full source-pair response sums are controlled, canonical sweep-stage representatives are preserved with exact prefix witnesses, exact vector telescoping is formalized, stage-residual energy is identified with sweep path loss, and a strictly positive volume-independent response cutoff with rhoResp < 1 is proved.
>
> The current finite-volume positive-beta frontier is no longer the old RMS / Harnack / stationarity obstruction. PR #4861 proves that the physical **full-minus-direct finite-update error** is charged to the exact sweep path-loss carrier. What remains is to identify or control the **direct finite-update part itself** by the ordered sweep/current-value Hilbert structure strongly enough to close the bounded-core six-spatial Poincare inequality. Only after that can the full genuine-joint L2 and finite-volume physical transfer-gap receiver be invoked.

## Repository authority

| Item | Current value |
| --- | --- |
| Theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Theorem-bearing baseline before this docs refresh | 693c2ef8673cdfe40ec6615fc7d9c3e600dc9745 |
| Latest merged theorem PR | #4861 |
| #4861 validated exact head | 8f4b83ea6388b1f654fb4b67a3407c3fa6b13d68 |
| #4861 CI | PR Lean Fast Check run 36313199617 — success |
| #4861 completion receipt | chatgpt-ci-receipt/PR Lean Fast Check — success |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |
| Default branch | main — not theorem authority |

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. historical summaries or memory.

A later docs-only merge may advance the branch pointer without changing the theorem-bearing mathematical baseline above.

## Proof spine at a glance

~~~text
FINITE WILSON / OS / PHYSICAL TRANSFER ROOT
  -> periodic SU(N) Wilson one-slab kernel
  -> OS / Gauss-law physical carrier
  -> compact positive physical transfer
  -> canonical nonnegative vacuum
  -> ground-state transformed boundary and joint laws
  -> genuine one-link / six-spatial conditional expectations

EXACT BETA-ZERO ENDPOINT
  -> vacuum = spatial Haar
  -> ground-state joint law = pair Haar
  -> kappa_0 = 1/6
  -> q_0 = 5/6
  -> exact physical transfer gap = 1

POSITIVE-BETA RESPONSE / SCHUR SIDE
  -> physical response and covariance kernels
  -> configuration-dependent envelope K_A(target,source)
  -> configuration-independent pin-free kernel K_pin(target,source)
  -> reciprocal shell row/column bounds
  -> bidirectional Schur contraction q_shell(s,beta) < 1
  -> transpose L2 action bound
  -> fixed-background response-amplitude matrix

RMS / TARGET RESIDUAL CLOSURE
  -> exact target-law response L2
  -> exact two-law RMS amplitude
  -> ordered first-cross Pythagorean split
  -> Harnack old-to-updated variance comparison
  -> exact stationarity return
  -> genuine target residual / canonical fiber variance
  -> strict RMS feedback absorption
  -> target-indexed and vacuum-integrated majorants

FIXED-BACKGROUND ENERGY ROUTE
  -> fixed-background RMS Fubini
  -> fixed-background response Fubini
  -> response amplitudes <= K_pin * target amplitudes
  -> transpose Schur on response amplitudes
  -> target amplitudes = genuine residual energy
  -> vacuum integration
  -> finite target sum = sum canonical fiber variances
  -> genuine CondExpL2 residual control

CANONICAL SWEEP / PHYSICAL RESPONSE ROUTE
  -> bounded sweep-stage representative for every spatial link
  -> preserve canonical prefix/suffix position
  -> exact vector telescoping of ordered projections
  -> canonical local profile = exact stage-residual norm
  -> sum stageResidual^2 = 6 * sweepPathLoss
  -> full response-sum energy
       <= rhoResp(s,beta) * ofReal(6 * sweepPathLoss)
  -> positive volume-independent betaResp(s)
  -> rhoResp(s,beta) < 1 on 0 <= beta <= betaResp(s)
  -> response energy <= ofReal(6 * sweepPathLoss)

EXACT PHYSICAL UPDATE DECOMPOSITION
  -> single-target fullDifferenceL2
       = directDifferenceL2 + responseL2
  -> semantic identification with actual source-updated centered means
  -> finite off-diagonal assembly
       fullOffDiagonalSum
         = directOffDiagonalSum + sum_target ResponseL2
  -> PR #4861:
       integral ||fullOffDiagonalSum - directOffDiagonalSum||^2
         <= rhoResp * ofReal(6 * sweepPathLoss)
  -> on strict cutoff:
       errorEnergy <= ofReal(6 * sweepPathLoss)

CURRENT FRONTIER
  -> close the direct finite-update side against the canonical ordered sweep
  -> identify the resulting physical current-value state / sweep residual
  -> derive positive-beta bounded-core six-spatial Poincare
  -> extend to full genuine joint L2
  -> obtain volume-uniform finite-volume physical transfer gap
  -> thermodynamic / infinite-volume construction
  -> continuum OS / Wightman reconstruction
  -> continuum Yang--Mills mass gap
~~~

## What is closed since the previous #4787 documentation snapshot

### #4791--#4799 — stationarity return and genuine target residual reconnection

The former #4787 frontier is closed.

The old-to-updated target variance comparison is integrated over the ordered law; the second-updated background is returned by exact stationarity / pushforward; the updated variance is identified with the reference target residual; and the first-cross energy is bounded by the genuine target-residual carrier.

In particular, the old statement

~~~text
updated variance outer integration / stationarity return OPEN
~~~

is obsolete.

### #4800--#4818 — second-mean RMS feedback and vacuum response energy

The second-law-mean RMS is packaged in source-pair L2, split exactly, transported across the ordered laws, and controlled by genuine target residual energy plus response feedback.

The feedback coefficient is made strict and absorbed. This yields target-indexed RMS majorants, global/vacuum target-residual majorants, response-energy matrices, and square-root response amplitudes.

### #4819--#4830 — current-value dependent route and the pointwise obstruction

A concrete current-value assembled state was built in source-dependent fixed-background L2 carriers:

~~~text
state_source
  = localPart_source + sum_target response_source,target.
~~~

The exact localPart energy was identified with target residual energy.

This route exposed an important boundary: an outer-energy RMS estimate does **not** justify pointwise-in-background domination needed by the earlier dependent transpose recurrence. That pointwise majorization was therefore not asserted.

### #4831--#4840 — fixed-background energy pivot and bidirectional pin-free Schur

The proof was reorganized at the energy level rather than forcing an unjustified pointwise RMS bound.

Closed steps include:

- exact fixed-background RMS Fubini;
- fixed-background RMS target majorant;
- exact fixed-background response Fubini;
- response energy <= target majorant;
- response amplitudes from square roots;
- reciprocal-weight row bound;
- uniform reciprocal shell mass;
- beta-zero-vanishing bootstrap envelope;
- configuration-independent row and column bounds for K_pin;
- bidirectional Schur contraction.

The key orientation remains:

~~~text
K_pin(target,source).
~~~

### #4841--#4849 — response energy to genuine residual and actual full response sums

The fixed-background response-amplitude matrix is fed through transpose Schur.

Target amplitude energy is identified with genuine target residual energy. The coefficient rhoResp is shown finite and zero at beta = 0. The bound is integrated over the physical vacuum.

A measurability bridge allows the finite target sum to commute exactly with the vacuum lower integral:

~~~text
integral_C sum_target E_target(C,target)
  =
sum_target CanonicalFiberVariance(target).
~~~

Canonical sweep-stage representatives are then selected simultaneously, and the actual full source-pair response sums satisfy a genuine Hilbert-space bound with no finite-cardinality Cauchy loss.

### #4850--#4852 — exact target-law L2 decomposition and finite target assembly

Three target means are realized in one source-specific Hilbert carrier.

For every off-diagonal target/source pair:

~~~text
fullDifferenceL2
  =
directDifferenceL2 + responseL2.
~~~

The auxiliary L2 objects are identified with the actual physical source-updated centered means.

After finite assembly and diagonal response cancellation:

~~~text
fullOffDiagonalSum(source)
  =
directOffDiagonalSum(source)
  + sum_target ResponseL2(source,target).
~~~

This is an exact Hilbert-space equality.

### #4853--#4858 — canonical prefix witnesses and exact sweep path loss

The canonical position of every stage representative is retained explicitly:

~~~text
canonicalList = pre ++ e :: suffix.
~~~

Generic vector telescoping is formalized:

~~~text
residualVectorSum(P, cs, x)
  =
x - sweep(P, cs, x).
~~~

For the canonical duplicate-free one-link sweep, each local-profile entry is exactly the norm of its unique stage residual. Therefore

~~~text
(1/6) * sum_e ||stageResidual_e||^2
  =
sweepPathLoss(f),

sum_e ||stageResidual_e||^2
  =
6 * sweepPathLoss(f).
~~~

The complete response energy is consequently charged directly to this exact path-loss carrier.

### #4859--#4860 — strict positive-beta response cutoff

Continuity at beta = 0 and the endpoint identity rhoResp(s,0)=0 yield a strictly positive, volume-independent cutoff

~~~text
betaResp(s) > 0
~~~

for every fixed s > 8 such that

~~~text
0 <= beta <= betaResp(s)
  =>
rhoResp(s,beta) < 1.
~~~

This cutoff lies inside the already validated bidirectional shell cutoff.

Hence the complete response energy obeys

~~~text
responseEnergy
  <=
ofReal(6 * sweepPathLoss(f))
~~~

on the strict-response interval.

### #4861 — physical full-minus-direct update error

PR #4861 reconnects the response-energy result to the exact physical finite-update decomposition:

~~~text
fullOffDiagonalSum - directOffDiagonalSum
  =
sum_target ResponseL2.
~~~

Thus

~~~text
errorEnergy
  <=
rhoResp(s,beta) * ofReal(6 * sweepPathLoss(f)),
~~~

and on the strict cutoff,

~~~text
errorEnergy
  <=
ofReal(6 * sweepPathLoss(f)).
~~~

This is the current theorem-bearing endpoint.

## Current mathematical frontier

The following are **closed and should not be rebuilt**:

- old/upated variance Harnack comparison;
- outer stationarity return;
- target-residual reconnection;
- second-mean RMS feedback;
- fixed-background Fubini;
- pin-free bidirectional Schur;
- response-amplitude transpose contraction;
- vacuum target-sum exchange;
- canonical prefix witnesses;
- exact vector sweep telescoping;
- local-profile = stage-residual norm;
- stage-residual energy = sweep path loss;
- positive strict response cutoff;
- full-minus-direct update-error control.

The remaining finite-volume step is narrower:

1. identify or sharply control the **direct off-diagonal finite-update sum** using the preserved ordered sweep-stage structure;
2. combine that with #4861 to control the corresponding full physical update/current-value state;
3. convert the result into a bounded-core six-spatial frame/Poincare inequality with a volume-independent positive constant on the strict-response beta interval;
4. only then invoke the existing full-L2 and physical transfer-gap receivers.

A key boundary must be preserved:

> #4861 controls the error between the full and direct finite-update sums. It does **not** yet prove the bounded-core Poincare inequality and does **not** identify that error energy with the centered global norm.

No numerical positive-beta Poincare constant should be frozen until the direct/full update-to-sweep normalization is formally closed.

## Lean / mathlib engineering discipline

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Operational rules:

- fresh theorem-carrier and exact PR head before branch creation, CI judgment, and merge;
- classify only the current exact head SHA;
- require terminal success of Changed Lean fast check and the exact-head receipt for theorem-bearing PRs;
- docs-only changes do not require rerunning Strict Lean when no Lean file changes;
- on RED, inspect the full changed module, CompileSmoke, imports, dependent signatures, and pinned APIs;
- distinguish static/import/cache failures from actual Lean elaboration failures;
- pinned mathlib is authority; current upstream can guide syntax only;
- preserve K(target,source) orientation;
- do not pointwise evaluate arbitrary L2 quotient representatives;
- do not introduce finite-cardinality Cauchy/telescoping losses;
- retain coefficient-one local residual results when already proved;
- for complex finite sums inside norms, prefer named Hilbert objects or explicit Finset.sum over parser-fragile nested notation;
- after Lp.coefFn additive identities, normalize pointwise function application explicitly before rewriting when needed.

## Status summary

~~~text
finite Wilson / OS / physical-transfer root                 CLOSED
exact beta-zero endpoint                                    CLOSED
positive-beta physical response / Schur side                CLOSED
old-to-updated variance stationarity return                 CLOSED
genuine target-residual reconnection                        CLOSED
second-mean RMS feedback                                    CLOSED
fixed-background RMS / response Fubini                      CLOSED
configuration-independent bidirectional K_pin Schur         CLOSED
vacuum finite target-sum exchange                           CLOSED
actual full source-pair response-sum energy                 CLOSED
single-target full = direct + response L2 decomposition     CLOSED
finite off-diagonal full/direct/response assembly           CLOSED
canonical sweep prefix witnesses                            CLOSED
exact vector sweep telescoping                              CLOSED
local profile = exact stage residual norm                   CLOSED
stage residual energy = 6 * sweep path loss                CLOSED
strict positive response cutoff rhoResp < 1                 CLOSED
full-minus-direct update error <= sweep path loss           CLOSED

direct finite-update -> ordered sweep/current-value closure OPEN
positive-beta bounded-core six-spatial Poincare             OPEN
full-L2 positive-beta finite-volume physical gap            OPEN
thermodynamic / infinite-volume construction                OPEN
continuum OS / Wightman construction                        OPEN
continuum Yang--Mills mass gap                              OPEN
~~~

## Navigation

- ROADMAP.md — exact restart point and next theorem sequence.
- MGAP4D/MathlibAnalytic — formal analytic development.
- theorem-carrier branch — formal/real-hilbert-uniform-coercive-strong-limit.
