# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository develops a finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer framework, exact beta-zero geometry, positive-beta response control, genuine ground-state conditional expectations, Hilbert-space sweep/coercivity machinery, and downstream thermodynamic / continuum infrastructure.

## Current status — 2026-09-27 JST

The unique authoritative theorem-carrier branch is:

**formal/real-hilbert-uniform-coercive-strong-limit**

The fresh theorem-bearing baseline immediately before this documentation refresh is:

**f8b2cea5a780ae88362b17b7e404c937168d85fa**

This is the merge commit of PR **#4869**, **Transport backward direct variance by Harnack**.

Validated exact head of #4869:

**518ac2f99b341106e7b1f00f7726292d53c96fd6**

Validation:

- PR Lean Fast Check run **36323111870 — success**
- exact-head completion receipt **chatgpt-ci-receipt/PR Lean Fast Check — success**

The default branch **main is not theorem authority**.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> What is now integrated is substantially beyond the previous #4787 documentation snapshot. The updated-variance stationarity return, genuine target-residual reconnection, second-mean RMS feedback chain, fixed-background response-energy route, configuration-independent bidirectional pin-free Schur kernel, actual full source-pair response sums, canonical prefix witnesses, exact vector telescoping, stage-residual path-loss identity, and the strict positive response cutoff are all closed.
>
> PR #4861 remains the exact response-side physical update theorem: the full-minus-direct finite-update error is charged to the canonical sweep path-loss carrier. The direct side has now advanced through PRs #4864--#4869. The actual DirectDifferenceL2 squared norm is identified exactly, bounded with coefficient one by the ordered direct average, transported losslessly to the backward reversible heat-bath carrier, split Pythagoreanly into centered variance plus squared backward mean, and the centered variance is transported by the existing volume-independent Harnack law factor back to the diagonal source law.
>
> The current finite-volume positive-beta frontier is therefore narrower than the #4861 snapshot. What remains is to identify the diagonal backward variance with the genuine one-link residual/canonical fiber-variance machinery, close the backward mean through its exact localPart + source-law-response split, and only then assemble the finite target/source sums without a volume-dependent cardinality loss. That direct closure must then be combined with #4861 to obtain the bounded-core six-spatial Poincare inequality.

## Repository authority

| Item | Current value |
| --- | --- |
| Theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Theorem-bearing baseline before this docs refresh | f8b2cea5a780ae88362b17b7e404c937168d85fa |
| Latest merged theorem PR | #4869 |
| #4869 validated exact head | 518ac2f99b341106e7b1f00f7726292d53c96fd6 |
| #4869 CI | PR Lean Fast Check run 36323111870 — success |
| #4869 completion receipt | chatgpt-ci-receipt/PR Lean Fast Check — success |
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

DIRECT UPDATE ENERGY ROUTE
  -> PR #4864:
       ||DirectDifferenceL2(target,source)||^2
         = source-pair integral of actual directMeanDifference^2
  -> PR #4865:
       ||DirectDifferenceL2||^2
         <= orderedDirectAverageEnergy
       with coefficient one
  -> PR #4867:
       ofReal ||DirectDifferenceL2||^2
         <= integral backwardDirectFiberEnergy
       on the reversible target heat-bath carrier
  -> PR #4868 exact Pythagoras:
       backwardDirectFiberEnergy
         = ofReal(backwardDirectVarianceEnergy)
           + ofReal(backwardDirectMean^2)
  -> PR #4869 for source != target and D=C[target<-g]:
       ofReal backwardDirectVarianceEnergy(C,D)
         <= ofReal((exp(32*beta))^2)
            * ofReal backwardDirectVarianceEnergy(C,C)

CURRENT FRONTIER
  -> identify diagonal backward variance with genuine source residual / canonical fiber variance
  -> close backwardDirectMean = localPart + sourceLawResponse without factor-two loss
  -> assemble direct finite-update sums without target/source cardinality loss
  -> connect the resulting direct energy to canonical stage residuals / sweepPathLoss
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

This remains the current response-side physical update endpoint; the direct side is advanced further by PRs #4864--#4869 below.

### #4864--#4869 — direct L2 energy to backward variance transport

The direct finite-update route has now crossed the carrier-theoretic part of the previous frontier.

PR #4864 proves the exact semantic energy identity

~~~text
||DirectDifferenceL2(target,source)||^2
  =
integral_(source-pair background)
  actualDirectMeanDifference^2.
~~~

PR #4865 then uses the already established one-fiber probability-space estimate and exact law reordering to obtain, with coefficient one,

~~~text
||DirectDifferenceL2(target,source)||^2
  <=
orderedDirectAverageEnergy(target,source).
~~~

PR #4867 transports this to the reversible backward heat-bath carrier:

~~~text
ofReal ||DirectDifferenceL2(target,source)||^2
  <=
integral_(target heat-bath joint law)
  BackwardDirectFiberEnergy(source).
~~~

PR #4868 splits the backward fiber energy exactly, pointwise in the old/new target-background pair:

~~~text
BackwardDirectFiberEnergy
  =
ofReal(BackwardDirectVarianceEnergy)
  + ofReal(BackwardDirectMean^2).
~~~

No triangle inequality or factor two is used.

Finally PR #4869 transports only the centered-variance component across a single off-diagonal target update. For source != target and D = C[target <- g],

~~~text
ofReal BackwardDirectVarianceEnergy(C,D)
  <=
ofReal((exp(32 * beta))^2)
  * ofReal BackwardDirectVarianceEnergy(C,C).
~~~

The orientation is fixed:

~~~text
fiber = source,
backgroundFiber = target.
~~~

Thus the centered variance is now back on the diagonal source law. The remaining direct-side work is no longer the earlier source-pair/ordered-law carrier conversion.

## Current mathematical frontier

The following are **closed and should not be rebuilt**:

- old/updated target-variance Harnack comparison and stationarity return;
- target-residual reconnection;
- second-mean RMS feedback;
- fixed-background response Fubini and bidirectional Schur;
- response-amplitude transpose contraction;
- vacuum target-sum exchange;
- canonical prefix witnesses and exact vector sweep telescoping;
- local-profile = exact stage-residual norm;
- stage-residual energy = sweep path loss;
- positive strict response cutoff;
- full-minus-direct update-error control from #4861;
- exact DirectDifferenceL2 energy realization from #4864;
- coefficient-one direct L2 -> ordered direct average bound from #4865;
- lossless ordered -> backward heat-bath carrier transport from #4867;
- exact backward direct fiber Pythagorean split from #4868;
- backward centered-variance Harnack transport to the diagonal source law from #4869.

The remaining finite-volume direct obstruction is now split into two explicit pieces.

1. **Diagonal variance piece.** Identify BackwardDirectVarianceEnergy(C,C) exactly, or with coefficient one, with the genuine source one-link residual / canonical fiber variance of the selected sweep-stage representative, then connect it to the exact stage-residual/path-loss carrier already closed in #4856--#4858.

2. **Backward mean piece.** Reuse the exact #4736 identity BackwardDirectMean = DiagonalLocalMean + BackwardLawResponse. Control the law-response part without using an arbitrary factor-two inequality and retain the coefficient-one localPart energy already established.

3. **Finite assembly only afterward.** Sum over targets/sources only once an orthogonal, Schur, or exact telescoping structure is available. Do not use finite-cardinality Cauchy or a factor proportional to the number of links.

4. Combine the resulting direct bound with #4861 and derive the bounded-core six-spatial Poincare inequality with a volume-independent positive constant on a certified positive-beta interval.

A key boundary remains:

> #4869 closes a one-target centered-variance transport theorem. It does **not** yet control the complete directOffDiagonalSum, and it does **not** yet prove the bounded-core Poincare inequality.

No numerical positive-beta Poincare constant should be frozen until the diagonal-variance, backward-mean, and finite-assembly normalizations are formally closed.

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
- after Lp.coeFn additive identities, normalize pointwise function application explicitly before rewriting when needed;
- a private theorem from one Lean module is not an API for another module: reconstruct the needed fact from public mathlib lemmas or expose a public theorem explicitly; #4868 uses public variance APIs rather than depending on #4782's private local Pythagoras lemma.

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
DirectDifferenceL2 exact energy realization                  CLOSED
direct L2 -> ordered direct average, coefficient one         CLOSED
ordered direct energy -> backward heat-bath carrier          CLOSED
backward direct fiber exact Pythagorean split                CLOSED
backward variance Harnack -> diagonal source law             CLOSED

diagonal backward variance -> genuine residual/path loss     OPEN
backward mean local/law-response energy closure              OPEN
direct finite target/source assembly without cardinality loss OPEN
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
