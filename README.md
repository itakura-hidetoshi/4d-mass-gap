# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository develops a finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer framework, exact beta-zero geometry, positive-beta response and covariance control, genuine ground-state conditional expectations, Hilbert-space coercivity receivers, and downstream thermodynamic/continuum infrastructure.

## Current status — 2026-09-24 JST

The unique authoritative theorem-carrier branch is:

**formal/real-hilbert-uniform-coercive-strong-limit**

Fresh authoritative theorem-bearing baseline at this documentation refresh:

**f22fbd1db7325dfe2da08e90b278b3bd14976b89**

This is the merge commit of PR #4704, **Apply physical RMS Harnack to bounded-concrete ground-state sections**.

The default branch **main** is a public landing/documentation branch and is **not** theorem authority.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> What is integrated is a substantial finite-volume Wilson/OS/physical-transfer theorem spine. The beta-zero endpoint is closed. The positive-beta physical influence matrix has a volume-independent bidirectional Schur coefficient. The six-spatial sweep local energy is a genuine link-indexed L2 profile. Bounded-concrete representatives survive all canonical sweep prefixes and satisfy the sharp Haar one-link theorem stage by stage.
>
> In addition, the former sup-norm bottleneck in local conditional-law transport has now been replaced by a formal RMS/L2 likelihood-ratio spine: weighted residual energy, exact overlap-coupling RMS energy, quadratic density-defect control, integrated Cauchy transport, normalized-weight transport, the actual continuous-vacuum physical one-link RMS Harnack theorem, and finally an automatic bounded-concrete wrapper.
>
> The current obstruction is therefore narrower than at #4693: assemble these stagewise/local RMS certificates along the existing hybrid/trajectory machinery into the actual observable-specific profile u_e(F), prove the one-sided recurrence against the already-defined **full physical influence envelope K**, and then prove a volume-free global profile majorant.

## Repository authority

| Item | Current value |
| --- | --- |
| Theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Current theorem-bearing baseline | f22fbd1db7325dfe2da08e90b278b3bd14976b89 |
| Latest merged theorem PR | #4704 |
| #4704 validated exact head | aa6a32a597d0920bc1a4305f4c6c63357b6bee76 |
| #4704 CI | PR Lean Fast Check #14946 / run 35972259556 — success |
| #4703 validated exact head | 690518df93d0654284f3e674f7222332e8372239 |
| #4703 CI | PR Lean Fast Check #14943 / run 35962807067 — success |
| #4702 validated exact head | e383e7252935af64dcdb4d21cbf624b541ceb6a6 |
| #4702 CI | PR Lean Fast Check #14934 / run 35958592059 — success |
| #4701 validated exact head | 7570aef3cc221c66d77c094ae1ee2bbd30c86af8 |
| #4701 CI | PR Lean Fast Check #14931 / run 35955246261 — success |
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

HIGH-TEMPERATURE PHYSICAL RESPONSE / INFLUENCE              #4634-#4648
  -> fixed-right response continuity
  -> physical influence / resolvent propagation
  -> covariance decay and shell summability
  -> beta-zero-vanishing remote residual
  -> positive volume-independent strict physical sweep interval

GENUINE GROUND-STATE L2 RECEIVERS                           #4650-#4652
  -> bounded-concrete -> full joint L2 closure
  -> six-spatial frame / random-scan Rayleigh receiver
  -> physical transfer-gap receiver

EXACT BETA-ZERO PHYSICAL ENDPOINT                           #4653-#4682
  -> exact physical transfer gap = 1
  -> literal pair-Haar six-spatial geometry
  -> kappa_0 = 1/6, q_0 = 5/6
  -> six-spatial consistency lower bound gap >= 1/16

POSITIVE-BETA BIDIRECTIONAL SCHUR L2                        #4683-#4687
  -> actual physical envelope K
  -> volume/background-independent q_phys < 1
  -> row and column control
  -> genuine L2 Schur estimate
  -> one-sided profile coercivity receiver

SWEEP LOCAL-ENERGY / BOUNDED-CORE BRIDGE                    #4688-#4693
  -> ordered sweep path loss <= block residual
  -> genuine six-spatial specialization
  -> link-indexed local profile ell_e
  -> (1/6) sum_e ell_e^2 <= E_6sp
  -> bounded-concrete sweep-prefix invariance
  -> stagewise sharp Haar one-link coercivity

PHYSICAL RMS / LIKELIHOOD-RATIO BRIDGE                      #4695-#4704
  -> bounded-concrete section -> actual physical envelope for bounded tests
  -> centered-radius strongly-measurable transport
  -> weighted residual-density energy control
  -> exact overlap-coupling RMS energy control
  -> quadratic likelihood-ratio density defect
  -> integrated ENNReal and real-L1 quadratic defect
  -> centered expectation Cauchy bound with linear influence
  -> normalized real-weight RMS transport
  -> actual physical one-link RMS background-update Harnack
  -> bounded-concrete ground-state section wrapper

CURRENT ANALYTIC FRONTIER
  -> apply #4704 at the #4693 canonical sweep stages
  -> reuse #852-#906 hybrid/trajectory geometry
  -> construct actual nonnegative profile u_e(F)
  -> transport local RMS changes through the full physical envelope K
  -> prove u_t <= ell_t + sum_s K_ts u_s
  -> prove a volume-free global profile majorant
  -> #4691 bounded-core six-spatial Poincare
  -> #4650 full joint L2
  -> #4651 volume-independent positive-beta physical transfer gap
  -> thermodynamic / continuum construction
~~~

## 1. Beta-zero endpoint is closed

The exact finite-volume beta-zero endpoint is no longer a frontier.

~~~text
kappa_0 = 1/6
q_0 = 5/6
gap(0) >= 1/16        -- six-spatial receiver consistency bound
gap(0) = 1            -- independent exact endpoint theorem
~~~

The value 1/16 is intentionally retained as a **non-optimal consistency receipt** for the six-spatial L2 route. It is not the exact beta-zero gap.

## 2. Positive-beta physical matrix / Schur side is closed

PRs #4683-#4687 close the finite-dimensional Schur side for the actual physical influence envelope K.

~~~text
q_phys(s,beta) = 18 * eta(beta) + rho_osc(s,beta)
0 <= q_phys(s,beta) < 1

maxRow(K)    <= q_phys
maxColumn(K) <= q_phys

sum_t (sum_s K_ts v_s)^2
  <= q_phys^2 * sum_s v_s^2.
~~~

Whenever nonnegative profiles u, ell satisfy

~~~text
u_t <= ell_t + sum_s K_ts u_s,
~~~

the existing receiver gives

~~~text
(1-q_phys)^2 * sum_t u_t^2
  <= sum_t ell_t^2.
~~~

This is a genuine L2 Schur theorem. Bounded-test/TV contraction is not being relabeled as an L2 Poincare theorem.

## 3. Sweep local energy and stagewise sharp Haar are closed

PRs #4688-#4690 show that ordered one-link sweep loss is controlled without a color-class cardinality factor:

~~~text
(1/6) * sum_e ell_e(f)^2
  = SixSpatialOneLinkSweepPathLoss(f)
  <= E_6sp(f).
~~~

PR #4691 feeds this exact ell_e into the #4687 receiver.

PR #4692 proves that every one-link update, finite same-color sweep, and canonical sweep prefix preserves the bounded-concrete core.

PR #4693 therefore provides, at every canonical sweep stage x_cs, an explicit bounded strongly measurable representative F_cs with

~~~text
SharpHaarVarianceFunctional(F_cs,e)
  <= ENNReal.ofReal (||x_cs - P_e x_cs||^2).
~~~

The exact sharp exp(-16 beta) coefficient remains inside the existing sharp Haar functional.

## 4. #4695: bounded-concrete sections reach the actual physical envelope

PR #4695 is the first direct type/measure bridge from the current bounded-concrete ground-state representatives to the actual positive-beta physical influence envelope.

For a strongly measurable bounded one-link concrete section, the literal normalized physical one-link fiber laws satisfy the existing envelope estimate without requiring continuity.

The same PR also packages centered-radius scaling:

~~~text
|E_u phi - E_v phi|
  <= K_target,source * radius
~~~

whenever

~~~text
|phi - center| <= radius.
~~~

This remains a sup-radius statement. It is useful as an actual-K bridge, but by itself it is not yet the desired RMS/L2 recurrence.

## 5. #4696-#4697: residual mass becomes residual energy

PR #4696 strengthens likelihood-ratio influence from unmatched **mass** to arbitrary weighted residual **energy**.

~~~text
(p - min(p,q)) + (q - min(p,q)) = |p-q|.
~~~

Mutual likelihood-ratio domination yields the same sharp coefficient against p+q. After multiplying by an arbitrary nonnegative weight and integrating, the estimate remains valid.

The centered-square specialization allows weights of the form

~~~text
ofReal ((X-c)^2).
~~~

PR #4697 then lifts the exact overlap coupling itself to RMS energy. The diagonal branch contributes zero; the residual product branch is bounded by the left/right centered residual energies and hence by the same likelihood-ratio influence coefficient times the two full conditional centered energies.

This closes the old sup-norm bottleneck at the overlap-coupling level.

## 6. #4698-#4701: quadratic likelihood-ratio Cauchy spine

PR #4698 proves the pointwise quadratic density-defect estimate

~~~text
(p-q)^2 / (p+q)
  <= c(K)^2 * (p+q)
~~~

under mutual likelihood-ratio domination, together with the repository's full-L1 normalization.

PR #4699 integrates that defect in ENNReal form.

PR #4700 promotes it to an ordinary real Integrable function and real integral estimate.

PR #4701 then applies the pinned mathlib Hölder/Cauchy API to obtain

~~~text
| integral (X-c) * (p-q) |
  <= (2*c(K)) *
     sqrt ( integral (X-c)^2 * (p+q) ).
~~~

The crucial point is that after taking the square root the influence coefficient remains **linear**, exactly the structure required by a one-sided profile recurrence.

## 7. #4702-#4704: normalized physical RMS transport is closed locally

PR #4702 packages #4701 at the level of normalized real weighted probability measures.

If nonnegative weights w,v are mutually pointwise R-comparable, normalization costs one additional factor R:

~~~text
|E_w[X-c] - E_v[X-c]|
  <= 2*c(R^2) *
     sqrt(E_w[(X-c)^2] + E_v[(X-c)^2]).
~~~

PR #4703 specializes this to the actual continuous-vacuum physical one-link fiber under a background-link update. The final coefficient is not new: it is exactly the existing BackgroundUpdateHarnackInfluence(beta).

PR #4704 removes the explicit first- and second-moment hypotheses for bounded-concrete ground-state sections. Strong measurability, the existing pointwise bound on the concrete representative, and integrability of the physical fiber weight automatically supply all required moments.

Thus a #4693 sweep-stage representative can now be inserted into an actual physical one-link RMS background-update theorem without evaluating an arbitrary L2 quotient representative pointwise.

## 8. What is still open: assemble the actual physical profile

For a bounded-concrete observable F, define an actual nonnegative spatial-link profile

~~~text
u_e(F)
~~~

and prove

~~~text
u_t(F)
  <= ell_t(F)
     + sum_s K_ts u_s(F).
~~~

Available ingredients are now:

- #4687: actual full physical envelope K and uniform Schur coefficient;
- #4690: canonical sweep-stage local profile ell_e;
- #4693: bounded representative + sharp Haar control at every stage;
- #4695: actual-K bounded/centered-radius section transport;
- #4696-#4702: generic RMS likelihood-ratio/Cauchy transport;
- #4703-#4704: actual physical one-link RMS background-update transport on bounded-concrete sections;
- #852-#906: existing hybrid / target-trajectory / endpoint-coupling machinery.

The missing step is to assemble these into the actual trajectory/profile recurrence, especially to carry RMS control through the **full** physical envelope, including the remote/resolvent contribution, rather than only the local background-update Harnack coefficient.

Do not re-prove the Schur theorem, local sweep energy theorem, bounded-core invariance, or likelihood-ratio Cauchy spine.

## 9. The second remaining analytic obligation: global profile majorant

Even after the one-sided recurrence is constructed, a genuine global comparison remains necessary:

~~~text
||F-center(F)||_L2^2
  <= sum_e u_e(F)^2
~~~

or an equivalent independent-pair energy majorant on the genuine ground-state joint carrier.

The old raw Wilson hybrid profile already has a global pair majorant, but direct finite hybrid telescoping can introduce an edge-cardinality Cauchy factor. That cannot be imported blindly because it would destroy volume-uniformity.

## 10. Intended positive-beta chain

~~~text
#4693 stagewise bounded representative + sharp Haar
        |
        v
#4704 bounded-concrete physical RMS background transport
        +
#852-#906 hybrid / trajectory geometry
        +
#4695 actual physical envelope bridge
        |
        v
actual profile u_e(F)
        |
        v
u_t <= ell_t + sum_s K_ts u_s
        |
        v
#4687 / #4691 uniform Schur coercivity
        |
        v
volume-free global profile majorant
        |
        v
bounded-core six-spatial Poincare
        |
        v
#4650 full genuine joint L2
        |
        v
#4651 genuine six-spatial Rayleigh q(beta) < 1
        |
        v
volume-independent positive-beta physical transfer gap
        |
        v
thermodynamic / continuum OS-Wightman construction
        |
        v
continuum Yang--Mills mass gap
~~~

## 11. Recent theorem units

| PR | Role | Merge commit |
| --- | --- | --- |
| #4690 | link-indexed sweep-stage local profile | 199507d12c903539aad9265f2b6969fb2fca375c |
| #4691 | feed local profile into uniform Schur receiver | c99af54a38a0338cee680817d806745a055031f6 |
| #4692 | preserve bounded-concrete core through one-link sweeps | 911c5246f134e1ac4819e496c3bea2f2b288094c |
| #4693 | stagewise sharp Haar local coercivity | 73d90bb97eb1a906d1d11eec10314e1ce1feb518 |
| #4695 | bounded-concrete section -> actual physical influence envelope | 4a573e91d4600e7288b0df6e0a9498223b74c04a |
| #4696 | weighted conditional residual energy by sharp influence | fe7b2a445d2f5ea2b77ee37978c5e51f8f28fbf1 |
| #4697 | exact overlap coupling -> RMS influence energy | 0726c1a19b205374f82186d3ae751687dfc0aa57 |
| #4698 | quadratic likelihood-ratio influence bound | 6fc5ec72c2f91f25f966938151d1a93fcf995acf |
| #4699 | integrated quadratic likelihood-ratio defect | 3e8d4134a5b556f009c96952de91537787cdde1f |
| #4700 | real-L1 quadratic defect interface | 530312e734e2755650c9a97ad8237c47c94dc1ce |
| #4701 | centered expectation Cauchy from quadratic influence | 4ec500197478989987305c8773d729e3b0197888 |
| #4702 | normalized real-weight centered RMS transport | 3f92826baadbd9f7db2b28333ff2e0653c368fb5 |
| #4703 | actual physical one-link centered RMS Harnack | e9a0c73aec92865b0841bc912089cf001cb568ef |
| #4704 | bounded-concrete physical RMS Harnack wrapper | f22fbd1db7325dfe2da08e90b278b3bd14976b89 |

PR #4675 remains **closed / unmerged / superseded by #4676**.

## Lean / mathlib verification discipline

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Current engineering rules include:

- inspect the entire changed file, imports, CompileSmoke, and dependent API when CI fails;
- treat the pinned mathlib revision as authority rather than current master;
- distinguish retained and ambient measurable spaces explicitly in conditional-expectation proofs;
- do not pointwise evaluate arbitrary L2 quotient representatives;
- use MemLp.condExpL2_ae_eq_condExp for the ordinary-condExp / genuine-L2 bridge;
- prefer typed simpa using and explicit intermediate normal forms over broad coercion-sensitive reverse rw;
- for Pi-valued algebra, expose Pi.add_apply / pointwise operations before using ring tactics;
- for inequalities such as a+c <= b+d, prefer explicit add_le_add when left/right helper inference is ambiguous;
- remember that rw or calc may close the goal; do not append unconditional tactics after a closed goal;
- validate exact PR head, workflow completion, and exact-head completion receipt before merge;
- after docs-only merges, separate the current branch pointer from the theorem-bearing baseline.

## Navigation

- ROADMAP.md — detailed theorem status and restart instructions.
- MGAP4D/MathlibAnalytic — formal analytic development.
- theorem-carrier branch: formal/real-hilbert-uniform-coercive-strong-limit.

## Status summary

~~~text
matrix / Schur side                         CLOSED
six-spatial sweep local energy              CLOSED
link-indexed local profile ell_e            CLOSED
bounded-core sweep invariance               CLOSED
stagewise sharp Haar coercivity             CLOSED
generic RMS likelihood-ratio/Cauchy spine   CLOSED
actual local physical RMS Harnack           CLOSED
bounded-concrete physical RMS wrapper       CLOSED

stagewise hybrid/profile assembly           OPEN
full-K one-sided physical recurrence        OPEN
global profile majorant                     OPEN
positive-beta bounded-core Poincare         OPEN
full-L2 positive-beta gap                   OPEN
continuum mass gap                          OPEN
~~~

The most natural next theorem unit is now the **stagewise bounded-concrete physical RMS hybrid profile assembly**: feed the #4693 canonical sweep-stage representatives into #4704, reuse #852-#906 for trajectory composition, and package the resulting amplitudes into the actual u_e(F) needed by the #4687/#4691 one-sided Schur receiver.
