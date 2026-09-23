# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository develops a finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer framework, exact beta-zero geometry, positive-beta response and covariance control, genuine ground-state conditional expectations, Hilbert-space coercivity receivers, and downstream thermodynamic/continuum infrastructure.

## Current status — 2026-09-24 JST

The unique authoritative theorem-carrier branch is:

**formal/real-hilbert-uniform-coercive-strong-limit**

Fresh theorem-bearing baseline at this documentation refresh:

**73d90bb97eb1a906d1d11eec10314e1ce1feb518**

This is the merge commit of PR #4693, **Apply sharp Haar bound at ground-state sweep stages**.

The default branch **main** is a public landing/documentation branch and is **not** theorem authority.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> What is integrated is a substantial finite-volume Wilson/OS/physical-transfer theorem spine. The beta-zero endpoint is closed, the positive-beta physical influence matrix has a volume-independent bidirectional Schur coefficient, the six-spatial local sweep energy has been realized as a genuine link-indexed L2 profile, and the bounded-concrete sharp one-link Haar theorem is now available at every canonical sweep stage.
>
> The current obstruction is no longer matrix contraction. It is the observable-specific analytic bridge: construct the actual ground-state physical profile (u_e(F)), prove its one-sided inequality against the already-defined physical envelope, and prove the corresponding global profile majorant. Only after that can the existing L2 receivers yield a volume-uniform positive-beta physical gap.

## Repository authority

| Item | Current value |
| --- | --- |
| Theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Current theorem-bearing baseline | `73d90bb97eb1a906d1d11eec10314e1ce1feb518` |
| Latest merged theorem PR | #4693 |
| #4693 validated exact head | `9ab9afc48a411529f7ba50b2c79cb9b2cda63066` |
| #4693 CI | PR Lean Fast Check #14910 / run 35933345632 — success |
| #4692 validated exact head | `82adb2203f0fdf3a1be38804be441e13d926eee8` |
| #4692 CI | PR Lean Fast Check #14908 / run 35932670460 — success |
| #4691 validated exact head | `0ab14ea94146adf3c35328d23aca5d36d8d2fdb8` |
| #4691 CI | PR Lean Fast Check #14901 / run 35929862853 — success |
| #4690 validated exact head | `8788b40b4a70aefe3ed7b5f45064c01a00f39ec2` |
| #4690 CI | PR Lean Fast Check #14899 / run 35929374564 — success |
| Lean | v4.30.0-rc2 |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Default branch | `main` — not theorem authority |

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. historical summaries or memory.

A later docs-only merge may advance the branch pointer without changing the theorem-bearing mathematical baseline.

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
  -> beta-zero-vanishing sharpened remote residual
  -> positive volume-independent strict physical sweep contraction

GENUINE GROUND-STATE L2 RECEIVERS                           #4650-#4652
  -> bounded-concrete -> full joint L2 closure
  -> six-spatial frame / random-scan Rayleigh receiver
  -> physical transfer-gap receiver
  -> abstract commuting-projection tensorization

EXACT BETA-ZERO PHYSICAL ENDPOINT                           #4653-#4682
  -> ambient and physical transfer are rank one at beta=0
  -> vacuum law = spatial Haar
  -> joint law = pair Haar
  -> exact physical transfer gap = 1
  -> literal six-color pair-Haar geometry
  -> kappa_0 = 1/6
  -> q_0 = 5/6
  -> physical endpoint bridge
  -> genuine ground-state transport
  -> six-spatial consistency lower bound gap >= 1/16

POSITIVE-BETA BIDIRECTIONAL SCHUR L2                        #4683-#4687
  -> generic finite nonnegative bidirectional Schur theorem
  -> isolate physical remote-row obstruction
  -> close row obstruction using oscillation covariance decay
  -> volume/background-independent q_phys(s,beta)
  -> max row <= q_phys and max column <= q_phys
  -> genuine L2 Schur estimate
  -> one-sided profile coercivity receiver

SWEEP LOCAL-ENERGY BRIDGE                                   #4688-#4693
  -> nested block projection dominates ordered sweep path loss
  -> genuine six-color one-link path loss <= six-spatial residual energy
  -> link-indexed nonnegative sweep-stage local profile ell_e
  -> (1/6) sum_e ell_e^2 <= E_6sp
  -> ell_e plugged into uniform Schur receiver
  -> bounded-concrete core preserved by every one-link sweep prefix
  -> sharp Haar one-link theorem available at every canonical sweep stage

CURRENT ANALYTIC FRONTIER
  -> construct actual observable-specific physical profile u_e(F)
  -> prove u_t <= ell_t + sum_s K_ts u_s
  -> prove a genuine global profile majorant
  -> combine with #4687/#4691 and #4690/#4693
  -> bounded-core positive-beta six-spatial Poincare
  -> #4650 full joint L2
  -> #4651 volume-independent physical transfer gap
  -> thermodynamic / continuum construction
~~~

## 1. Beta-zero endpoint is closed

The exact finite-volume beta-zero endpoint is no longer a frontier.

Canonical conclusions include

~~~text
kappa_0 = 1/6
q_0 = 5/6
gap(0) >= 1/16        -- six-spatial receiver consistency bound
gap(0) = 1            -- independent exact endpoint theorem
~~~

The value (1/16) is intentionally retained as a **non-optimal consistency receipt** for the six-spatial L2 route. It is not the exact beta-zero gap.

## 2. Positive-beta physical matrix side is closed

PRs #4683-#4687 close the finite-dimensional Schur side for the actual physical influence envelope.

The canonical volume/background-independent scalar is

~~~text
q_phys(s,beta)
  = 18 * eta(beta) + rho_osc(s,beta)
~~~

on the strict physical-sweep interval, with

~~~text
0 <= q_phys(s,beta) < 1.
~~~

For every finite volume (H) and physical background (A),

~~~text
maxRow(K_{H,A})    <= q_phys
maxColumn(K_{H,A}) <= q_phys.
~~~

Hence for every real link profile (v),

~~~text
sum_t (sum_s K_ts v_s)^2
  <= q_phys^2 * sum_s v_s^2.
~~~

And whenever nonnegative profiles (u,ell) satisfy

~~~text
u_t <= ell_t + sum_s K_ts u_s,
~~~

the existing receiver gives

~~~text
(1-q_phys)^2 * sum_t u_t^2
  <= sum_t ell_t^2.
~~~

This is a genuine L2 Schur/resolvent theorem. No bounded-test contraction is being relabeled as an L2 Poincare theorem.

## 3. The local-energy side is now link-indexed and volume-independent

PR #4688 proves a generic real-Hilbert theorem: if a stronger block projection (B) absorbs every projection in an ordered sweep, then without any commutativity assumption,

~~~text
PathLoss(P,cs,x) <= ||x - Bx||^2.
~~~

PR #4689 specializes this to the genuine ground-state six-spatial system. For every spatial color (c),

~~~text
PathLoss_c(f) <= ||f - P_c f||^2,
~~~

and therefore

~~~text
(1/6) * sum_c PathLoss_c(f)
  <= E_6sp(f).
~~~

No color-class cardinality factor appears.

PR #4690 then realizes those successive sweep residuals as a genuine nonnegative spatial-link profile (ell_e(f)):

~~~text
(1/6) * sum_e ell_e(f)^2
  = SixSpatialOneLinkSweepPathLoss(f)
  <= E_6sp(f).
~~~

This is the receiver-ready local profile.

## 4. The Schur receiver is connected to the concrete sweep profile

PR #4691 composes #4687 and #4690.

For any nonnegative profile (u_e) satisfying the still-observable-specific inequality

~~~text
u_t <= ell_t(f) + sum_s K_ts u_s,
~~~

Lean now proves

~~~text
(1/6) * (1-q_phys)^2 * sum_e u_e^2
  <= E_6sp(f).
~~~

A second theorem exposes the remaining global majorant as an explicit premise:

~~~text
||f - center(f)||^2 <= sum_e u_e^2
~~~

implies the corresponding relative Poincare inequality.

The coefficient contributed by the already-closed receiver is therefore explicit. The final physical coefficient should **not** be frozen until the actual observable-specific profile normalization, sharp one-link factor, and global majorant are connected.

## 5. Bounded-concrete sweep compatibility is closed

The sharp one-link theorem is formulated on bounded strongly measurable concrete representatives. To use it at sweep intermediates, the bounded-concrete core must survive conditional-expectation updates.

PR #4692 proves exactly this:

~~~text
f in boundedConcreteCore
  -> P_e f in boundedConcreteCore
  -> every finite same-color sweep of f is in boundedConcreteCore
  -> every canonical sweep prefix is in boundedConcreteCore.
~~~

The proof uses the ordinary conditional expectation to construct a retained-sigma-algebra representative, proves its essential bound by monotonicity and constant conditional expectations, replaces it by an everywhere bounded representative on a full-measure set, and identifies its L2 class with the genuine `condExpL2` projection.

No pointwise section of an arbitrary L2 quotient representative is used.

## 6. Sharp Haar local coercivity is now available at every sweep stage

PR #4693 combines #4692 with the pre-existing sharp bounded-core one-link theorem.

For every bounded-concrete input, finite same-color sweep prefix (cs), and next link (e), the stage vector

~~~text
x_cs = realHilbertProjectionSweep P cs f
~~~

admits an explicit bounded strongly measurable representative (F_{cs}) such that

~~~text
SharpHaarVarianceFunctional(F_cs,e)
  <= ENNReal.ofReal (||x_cs - P_e x_cs||^2).
~~~

Thus the sharp one-link local theorem can be applied at the exact intermediate vectors whose squared residuals form the #4690 path-loss profile.

The exact sharp coefficient (e^{-16eta}) remains carried inside the existing sharp Haar functional.

## 7. Current obstruction: construct the actual physical profile

The next theorem is **not** another matrix norm theorem and is **not** another abstract receiver.

For a bounded concrete ground-state observable (F), construct a genuine spatial-link profile (u_e(F)) from the already-integrated Wilson hybrid/trajectory machinery and prove

~~~text
u_t(F)
  <= ell_t(F)
     + sum_s K_ts u_s(F),
~~~

where

- (K) is the actual physical influence envelope already controlled by #4687;
- (ell_t(F)) is the canonical sweep-stage local profile from #4690;
- the local term is justified stage-by-stage using #4692/#4693 and the existing sharp Haar one-link theorem.

The older raw Wilson spine #852-#906 already contains the canonical hybrid pair profile, target trajectory, endpoint coupling, double trajectory, endpoint covariance, and conditional variance machinery. That infrastructure should be transported/reused rather than reconstructed from scratch.

## 8. The second remaining analytic obligation: global profile majorant

Even after the one-sided inequality, a genuine global comparison is required. Schematically:

~~~text
||F - center(F)||_L2^2
  <= sum_e u_e(F)^2
~~~

or an equivalent independent-pair global energy majorant on the correct ground-state joint carrier.

The raw Wilson hybrid profile already has a finite global pair majorant, but its direct canonical form includes the finite hybrid-path Cauchy cost. The positive-beta ground-state theorem must be connected without accidentally reintroducing an unacceptable volume-dependent constant.

This global majorant is therefore kept explicit as a separate obligation.

## 9. Intended positive-beta chain

~~~text
#4693 stagewise sharp one-link control
        +
#4690 sweep-stage local profile
        +
actual physical hybrid profile u_e(F)
        |
        v
observable-specific one-sided inequality
        |
        v
#4687 / #4691 uniform Schur coercivity
        |
        v
genuine global profile majorant
        |
        v
bounded-core six-spatial Poincare coefficient kappa(beta) > 0
        |
        v
#4650 dense bounded-core -> full genuine joint L2
        |
        v
#4651 genuine six-spatial Rayleigh q(beta) < 1
        |
        v
volume-independent positive-beta physical transfer gap
~~~

Only after this finite-volume physical gap is established does the thermodynamic/continuum program become the active frontier.

## 10. Recent theorem units

| PR | Role | Merge commit |
| --- | --- | --- |
| #4681 | exact genuine beta-zero physical six-spatial frame/Rayleigh package | `c0e01312d99171ed9bf7b936e65fbff1f7bf9e2a` |
| #4682 | transport beta-zero contraction to genuine ground-state L2; receiver lower bound | `1a37b2e19edf476eea37f3da54ec717bd28858ea` |
| #4683 | generic bidirectional Schur L2 theorem | `38ccad587e4497126ff06c406910163e08c74fdd` |
| #4684 | isolate physical remote-row obstruction | `3585bdafa89b4a266aec94dfb11bfc36f3e23f6c` |
| #4685 | connect row/column contraction to bidirectional Schur | `aca7489bb085874703e18f31ad1d569f67af18eb` |
| #4686 | close remote row with oscillation covariance decay | `6b60ae010004ae9224faeddadd76b17216c7909e` |
| #4687 | package uniform physical bidirectional Schur coefficient | `e0975339e85cd6c0d9d52a83fe9116540256946d` |
| #4688 | nested block projection dominates sweep path loss | `a4e6c95450945c10c0dc7257cd7a489b2cc2601a` |
| #4689 | genuine six-color one-link path-loss bridge | `96047c2028dbdc315bc0fa8af4ddf61d9f2fac71` |
| #4690 | realize path loss as link-indexed stage profile | `199507d12c903539aad9265f2b6969fb2fca375c` |
| #4691 | feed sweep-stage profile into uniform Schur receiver | `c99af54a38a0338cee680817d806745a055031f6` |
| #4692 | preserve bounded-concrete core through one-link sweeps | `911c5246f134e1ac4819e496c3bea2f2b288094c` |
| #4693 | apply sharp Haar bound at every sweep stage | `73d90bb97eb1a906d1d11eec10314e1ce1feb518` |

PR #4675 remains **closed / unmerged / superseded by #4676**.

## Lean / mathlib verification discipline

Pinned environment:

- Lean v4.30.0-rc2
- mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`

Current engineering rules include:

- inspect the entire changed file, imports, CompileSmoke, and dependent API when CI fails;
- treat the pinned mathlib revision as authority rather than current master;
- distinguish retained and ambient measurable spaces explicitly in `condExp` / `condExpL2` proofs;
- if local measurable-space definitions can be inferred as typeclass instances, restore the ambient instance explicitly before ordinary `StronglyMeasurable` arguments;
- keep dependent Lp transport narrow;
- prefer typed `simpa using` over broad `rw` for dependent Sigma sums and proof-indexed carriers;
- remember that `rw` may close a goal automatically;
- inspect the type of `add_le_add_left/right` rather than relying on the name;
- normalize finite color indices early when a receiver expects `Fin 6`;
- after parallel or docs-only merges, fresh-reobserve the theorem-carrier and separate the current pointer from the theorem-bearing baseline;
- merge only from an exact validated PR head with completed success and exact-head completion receipt.

## Navigation

- `ROADMAP.md` — detailed theorem status and restart instructions.
- `MGAP4D/MathlibAnalytic` — formal analytic development.
- theorem-carrier branch: `formal/real-hilbert-uniform-coercive-strong-limit`.

## Status summary

The present formal frontier is:

~~~text
matrix / Schur side                  CLOSED
six-spatial sweep local energy       CLOSED
link-indexed local profile ell_e     CLOSED
bounded-core sweep invariance        CLOSED
stagewise sharp Haar coercivity      CLOSED

actual physical profile u_e(F)       OPEN
one-sided physical profile inequality OPEN
global profile majorant              OPEN
positive-beta bounded-core Poincare  OPEN
full-L2 positive-beta gap            OPEN
continuum mass gap                   OPEN
~~~

The most natural next theorem unit is the **ground-state bounded-concrete physical hybrid one-sided profile**: reuse the #852-#906 hybrid/trajectory spine, specialize it to the current ground-state joint/physical conditional law, and prove the one-sided inequality against the #4687 physical envelope with #4690/#4693 providing the local term.
