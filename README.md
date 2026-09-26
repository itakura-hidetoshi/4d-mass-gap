# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository develops a finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer framework, exact beta-zero geometry, positive-beta physical response and covariance control, genuine ground-state conditional expectations, Hilbert-space coercivity receivers, and downstream thermodynamic / continuum infrastructure.

## Current status — 2026-09-26 JST

The unique authoritative theorem-carrier branch is:

**formal/real-hilbert-uniform-coercive-strong-limit**

The fresh theorem-bearing baseline immediately before this documentation refresh is:

**d1a2e7bb9189643cf7c973568fab5dd39065bbf6**

This is the merge commit of PR **#4787**, **Compare ordered old and updated target variances**.

The default branch **main is not theorem authority**.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> What is integrated is a substantial finite-volume Wilson / OS / physical-transfer theorem spine. The exact beta-zero endpoint is closed. The positive-beta physical Schur matrix side is closed. The six-spatial local-energy / localPart chain is closed with coefficient one. The observable-specific target-law response and exact two-law RMS amplitude now exist in source-pair L2. The remaining first-cross mismatch has been reduced, without a factor-two loss, to an updated target-fiber variance through an exact Pythagorean split and a sharp Harnack variance comparison.
>
> The immediate frontier is to integrate the #4787 pointwise old-to-updated variance inequality over the ordered outer law, use second-updated-background stationarity / pushforward to return that updated variance to the genuine target-residual carrier, and then close the actual target-indexed RMS majorant / transpose recurrence consumed by the already-proved Schur receiver.

## Repository authority

| Item | Current value |
| --- | --- |
| Theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Theorem-bearing baseline before this docs refresh | d1a2e7bb9189643cf7c973568fab5dd39065bbf6 |
| Latest merged theorem PR | #4787 |
| #4787 validated exact head | 05d6555377d6774c823e5d5d4318a5a858c95bd6 |
| #4787 CI | PR Lean Fast Check run 36213674095 — success |
| #4787 completion receipt | chatgpt-ci-receipt/PR Lean Fast Check — success |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |
| Default branch | main — not theorem authority |

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. historical summaries or memory.

A later docs-only merge may advance the theorem-carrier pointer without changing the theorem-bearing mathematical baseline above.

## Proof spine at a glance

~~~text
FINITE WILSON / OS / PHYSICAL TRANSFER ROOT
  -> periodic SU(N) Wilson one-slab kernel
  -> OS / Gauss-law physical carrier
  -> compact positive physical transfer
  -> canonical nonnegative vacuum
  -> ground-state transformed boundary and joint laws
  -> genuine one-link / six-color conditional expectations

EXACT BETA-ZERO ENDPOINT
  -> vacuum = spatial Haar
  -> ground-state joint law = pair Haar
  -> kappa_0 = 1/6
  -> q_0 = 5/6
  -> exact physical transfer gap = 1

POSITIVE-BETA MATRIX / RECEIVER SIDE
  -> canonical fixed-right response profile
  -> physical influence / covariance decay
  -> background-dependent envelope K_A
  -> volume-independent row + column Schur coefficient q_phys(s,beta) < 1
  -> ordinary + transpose one-sided Schur receivers
  -> arbitrary-outer-law / physical-vacuum Schur integration

SWEEP LOCAL ENERGY / localPart
  -> six-spatial stage profile ell_s
  -> (1/6) sum_s ell_s^2 <= E_6sp
  -> canonical fiber variance / genuine CondExp bridge
  -> genuine-joint canonical residual L2
  -> ||localPart_s|| <= ell_s with coefficient 1

OBSERVABLE-SPECIFIC RESPONSE / RMS                    #4775-#4779
  -> exact target-law response on source-pair carrier
  -> response L2(nu_source)
  -> exact two-law RMS amplitude L2(nu_source)
  -> ||Response|| <= K_pin(target,source) * ||RMS||
  -> response independent of scalar center
  -> pointwise center freedom for RMS
  -> choose actual second target-law mean as canonical center
  -> second centered mean = 0 exactly

FIRST-CROSS LAW MISMATCH                              #4780-#4785
  -> reorder source-pair law exactly to (C,v,g)
  -> expose literal mismatch:
       g ~ kappa_target(C)
       center/frozen section based at C[source <- v]
  -> exact Pythagorean split
       firstCrossEnergy
         = oldTargetVariance + response^2
  -> lift to ordered outer law
  -> ordered response^2 = ||ResponseL2||^2
  -> global exact split
       firstCrossEnergy
         = integral oldTargetVariance
           + ofReal(||ResponseL2||^2)

VARIANCE COMPARISON                                  #4786-#4787
  -> normalized physical one-link laws under one off-fiber
     background update are mutually dominated by
       K_H(beta) = (exp(32 beta))^2
  -> generic evariance transport under measure domination
  -> ordered old target variance <= K_H * updated target variance
     pointwise, with no triangle inequality / factor two

CURRENT FRONTIER
  -> integrate #4787 over the ordered outer law
  -> use exact second-updated-background stationarity / pushforward
  -> identify the updated variance integral with the genuine
     target-fiber residual/profile already linked to CondExpL2
  -> combine with #4785 and the response L2 bound
  -> close the actual target-indexed RMS majorant / transpose recurrence
  -> feed #4773 transpose Schur receiver
  -> positive-beta bounded-core six-spatial Poincare
  -> #4650 full genuine joint L2
  -> #4651 q(beta) < 1 and finite-volume physical transfer gap
  -> thermodynamic / infinite-volume construction
  -> continuum OS / Wightman reconstruction
  -> continuum Yang--Mills mass gap
~~~

## What changed after the #4774 documentation snapshot

### #4775--#4777 — concrete response and exact RMS are now actual L2 objects

PR #4775 realizes the actual observable-specific target-law response on the exact source-pair carrier.

PR #4776 packages that response as an element of the source-specific carrier

~~~text
E_source = L2(nu_source)
~~~

and preserves the physical response coefficient at the norm level.

PR #4777 names the two centered target-fiber energies, forms the exact RMS amplitude

~~~text
RMS(z) = sqrt(E_first(z) + E_second(z)),
~~~

packages it in the same source-pair L2 carrier, and proves the coefficient-preserving estimate

~~~text
||Response_{source,target}||
  <= K_pin(target,source) * ||RMS_{source,target}||.
~~~

No finite-cardinality Cauchy loss is introduced.

### #4778--#4779 — remove the artificial fixed-center obstruction

PR #4778 proves that the response itself is independent of the common scalar center. Therefore the response can be held at any reference center while the RMS energy uses a context-dependent pointwise center.

PR #4779 chooses the actual second target-law fiber mean as that center. Consequently,

~~~text
SecondMean(center = secondFiberMean) = 0
~~~

exactly.

This converts the remaining RMS difficulty into a single first-law cross energy.

### #4780--#4781 — put the first cross energy in literal ordered coordinates

PR #4780 transports the complete first-law cross energy exactly to

~~~text
mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).
~~~

PR #4781 removes the remaining carrier aliases and exposes the literal mismatch:

~~~text
sample law:       g ~ kappa_target(C)
frozen section:   X_v(g) = F(left, C[source <- v][target <- g])
centering mean:   mean under kappa_target(C[source <- v]).
~~~

No inequality has been used at this stage.

### #4782--#4785 — exact Pythagorean reduction and response-L2 closure

PR #4782 inserts the old-law mean and proves the exact Pythagorean identity

~~~text
E_old[(X_v - m_new)^2]
  =
Var_old(X_v)
  + (m_old - m_new)^2.
~~~

The mean gap is exactly the concrete target-law response. Therefore no factor two appears.

PR #4783 lifts this identity to the full ordered outer law.

PR #4784 identifies the ordered response-square integral exactly with

~~~text
ofReal(||ResponseL2||^2).
~~~

PR #4785 composes the results:

~~~text
firstCrossEnergy
  =
integral oldTargetVariance
  + ofReal(||ResponseL2||^2).
~~~

At this point the response-square contribution is no longer a new analytic unknown.

### #4786--#4787 — reduce old target variance to updated target variance

PR #4786 exposes the measure-level Harnack domination already implicit in the bounded-test theory and proves a generic variance transport theorem:

~~~text
mu <= K • nu
  =>
evariance_mu(X) <= K * evariance_nu(X).
~~~

For one physical background-link update the coefficient is

~~~text
K_H(beta) = (exp(32 beta))^2.
~~~

PR #4787 specializes this to the ordered first-cross carrier:

~~~text
ofReal(oldVariance(C,v))
  <=
K_H(beta) * ofReal(updatedVariance(C,v)).
~~~

This uses variance minimality and measure domination directly; it does not use a triangle inequality and therefore introduces no extra factor two.

## Current mathematical frontier

The old localPart obstruction is closed. The Schur matrix / outer integration algebra is closed. The concrete response and RMS carriers are closed. The law mismatch has been reduced to a single updated target-fiber variance.

The next theorem unit should perform the **outer integration and stationarity return**:

1. integrate the #4787 pointwise inequality over the ordered second-background law;
2. pull the constant Harnack factor outside the ENNReal integral without changing it;
3. use the exact second-updated-background stationarity / pushforward theorem to rewrite the updated variance integral on the genuine source/reference carrier;
4. identify that updated variance with the already-existing canonical target-fiber variance / genuine target residual profile;
5. combine with the #4785 exact split.

The intended schematic result is:

~~~text
firstCrossEnergy
  <=
K_H(beta) * genuineTargetVarianceEnergy
  + ofReal(||ResponseL2||^2).
~~~

Then use the already-proved response estimate

~~~text
||Response_{source,target}||
  <= K_pin(target,source) * ||RMS_{source,target}||
~~~

to close the target-indexed RMS majorant / transpose recurrence without reintroducing a finite-volume cardinality factor.

The required matrix orientation remains:

~~~text
K(target,source),
~~~

never K(source,target).

After the observable-specific recurrence is closed, feed it into the #4773 transpose outer-Schur receiver.

## Recent theorem units

| PR | Role | Merge commit |
| --- | --- | --- |
| #4775 | realize concrete target-law response on source-pair carrier | 828605b8527f2a35c729bafccd75691560fcb595 |
| #4776 | realize target-law response in source-pair L2 | 4b3409720569252ca7a258a59c138636837d1b68 |
| #4777 | realize exact target-law RMS amplitude in source-pair L2 | fee8782246351c60b50262212fb0a83ba007bfef |
| #4778 | prove response center freedom and pointwise-center RMS interface | 5d8425f94a9cb0f9ee3ab3b01ad91fa7a2988ef1 |
| #4779 | choose actual second-law fiber mean as canonical center | 09cb36cf91d175e673f5f98c59005e651a2342c7 |
| #4780 | reorder first cross energy exactly | 8b53b9e07efe22d117a62815e4e91c619d362ddc |
| #4781 | expose ordered first cross residual in literal coordinates | 253383daa562428ab4768a9a49dc425998b9097f |
| #4782 | exact Pythagorean split of first cross energy | e4953e7c0d3235051f85dd0263cfad2c34882fdd |
| #4783 | lift Pythagorean split to ordered outer law | 0d1d34c6920c9a3c4a9a79411ceb44422c359de5 |
| #4784 | identify ordered response square with response L2 norm-square | d5af7e9420fdfe7bf99d3e37e5e571fe0c9738f2 |
| #4785 | global split: old variance + response L2 norm-square | 150b8611f8a7d63ba347b893e263d008e91622af |
| #4786 | background-update Harnack evariance comparison | ab2dc7dcaa1b965e2b0aed94e0812c48ff1c06fc |
| #4787 | ordered old variance <= Harnack factor * updated variance | d1a2e7bb9189643cf7c973568fab5dd39065bbf6 |

PR #4774 was the previous docs-only refresh and is not a new theorem-bearing mathematical step.

## Lean / mathlib engineering discipline

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Current rules:

- fresh theorem-carrier and current PR head before branch creation, write, CI judgment, and merge judgment;
- classify only the PR's current exact head SHA;
- require terminal success of **Changed Lean fast check** and the exact-head completion receipt;
- on RED, inspect the full changed Lean module, CompileSmoke, imports, dependent signatures, and pinned API — not only the reported line;
- distinguish static dependency/preflight failures from actual Lean elaboration failures;
- pinned mathlib is authority; current upstream docs may guide syntax only;
- install theorem-proved probability / Markov structures locally with letI when typeclass APIs require them;
- do not pointwise evaluate arbitrary L2 quotient representatives;
- preserve source/target orientation K(target,source);
- avoid finite-cardinality Cauchy / telescoping losses.

Recent Lean 4 lessons that now matter operationally:

- ordinary rw matches with reducible transparency; if a local alias or wrapper hides the intended subterm, first normalize it with a typed intermediate equality or narrow simpa;
- unfold processes named definitions sequentially; open outer aliases before inner definitions if the outer alias reveals the inner one;
- change accepts only definitional equality; theorem-level identities such as sub_zero must be simplified before change;
- simpa using performs its final type match at reducible transparency;
- keep simp sets tight; unused simp arguments are a signal that the goal has already normalized through a different route;
- scalar action and multiplication are not always definitionally identical; normalize with smul_eq_mul when an ENNReal measure/integral theorem returns a smul form;
- give lambdas explicit domain types when expected-type inference is insufficient.

## Status summary

~~~text
finite Wilson / OS / physical-transfer root              CLOSED
exact beta-zero endpoint                                 CLOSED
positive-beta physical matrix / Schur side               CLOSED
six-spatial sweep local energy                           CLOSED
coefficient-one localPart chain                          CLOSED
source-specific response L2                              CLOSED
exact two-law RMS amplitude L2                           CLOSED
response center freedom                                  CLOSED
second-law canonical pointwise center                    CLOSED
ordered first-cross law reordering                       CLOSED
exact Pythagorean cross-energy split                     CLOSED
response-square -> response L2 norm-square               CLOSED
global cross-energy = old variance + response L2         CLOSED
background-update Harnack evariance tool                 CLOSED
ordered old variance -> updated variance                 CLOSED

updated variance outer integration / stationarity return OPEN
genuine target-residual/profile reconnection              OPEN
observable-specific target RMS majorant / recurrence      OPEN
positive-beta bounded-core Poincare                      OPEN
full-L2 positive-beta finite-volume gap                  OPEN
thermodynamic / continuum mass gap                       OPEN
~~~

## Navigation

- ROADMAP.md — detailed restart point and theorem sequence.
- MGAP4D/MathlibAnalytic — formal analytic development.
- theorem-carrier branch — formal/real-hilbert-uniform-coercive-strong-limit.
