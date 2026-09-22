# MGAP4D Roadmap

**Checkpoint: 2026-09-22 JST — integrated through PR #4634.**

This document records the construction order for `itakura-hidetoshi/4d-mass-gap`. It distinguishes integrated theorems, integrated conditional implications, and the next applications that have not yet been exported as repository theorems. See [README.md](README.md) for the current mathematical overview.

## Authority and exact continuation point

```text
Theorem-carrier branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Theorem-bearing mathematical baseline:
  0bf8813960a5273da4348e4521b44c10bd20893d

Baseline PR:
  #4634 — Prove joint continuity of the literal fixed-right target-ratio response

Validated PR head:
  6c4f22b0788abef884a5f0aaef360d2c3171d369
```

[PR #4634](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4634) is merged. Its [merge commit](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/0bf8813960a5273da4348e4521b44c10bd20893d) is the mathematical baseline above. Later README/ROADMAP-only commits are documentation changes, not additional Lean theorems. `main` is the public documentation surface, not theorem authority; synchronizing these documents must not merge the theorem history into `main`.

Authority remains: fresh exact GitHub theorem-carrier SHA > formal Lean artifacts > README/ROADMAP > CI receipts > history/memory. Read the current branch again at each continuation; do not assume this checkpoint is still its newest pointer.

## Development map

```text
A. FINITE WILSON / OS / PHYSICAL TRANSFER                  integrated
B. EXACT ONE-LINK LAWS / CONDITIONAL EXPECTATION           integrated
C. FIXED-VOLUME COVARIANCE-REMAINDER REMOVAL                integrated
D. LOCAL WEIGHTED HARNACK / GREEN THEORY                   through #4560
E. CANONICAL R_can / PIN-FREE RESPONSE RECURRENCE           through #4595
F. AGGREGATE REMOTE FAMILY / LOCAL C5 COLUMN               through #4603
G. EXACT M_can / HALF-BARRIER / CONTINUITY REDUCTION        through #4608
H. TRANSFER / RESOLVENT / FIXED RIESZ CONTOUR               through #4613
I. CONTOUR CONTINUITY / TOP RANK / IDEMPOTENCE              through #4625
J. RANK PERSISTENCE / Q_beta = P_beta / PROJECTOR CONTINUITY closed #4628-#4629
K. EXISTING NONNEGATIVE NORMALIZED L2 VACUUM CONTINUITY     closed #4630
L. EXISTING CONTINUOUS VACUUM / SUP NORM / RECIPROCAL       closed #4631
M. COMPACT WEIGHTED-PROBABILITY CONTINUITY                  closed #4632
N. ACTUAL FIXED-RIGHT DENSITY / LAW EXPECTATIONS            closed #4633
O. LITERAL TARGET-RATIO RESPONSE JOINT CONTINUITY          closed #4634
P. ORIGINAL R_can COMPACT-SUPREMUM CONNECTION              OPEN NOW
Q. ACTUAL M_can CONTINUITY / HALF-BARRIER DISCHARGE         after P
R. STRICT WEIGHTED PHYSICAL INFLUENCE / SPATIAL DECAY       downstream
S. COVARIANCE / REMOTE RESIDUAL / COERCIVITY / UNIFORM GAP  downstream
T. THERMODYNAMIC / CONTINUUM PHYSICAL CONSTRUCTION         downstream
```

The former #4625 frontier has been closed through the actual response. Do not restart rank persistence, projector identification, or vacuum selection as though they were still missing. The first unfinished connection is the supremum defining `R_can`.

## Integrated foundation: original phases 1-14

The earlier phase numbers are retained here as a history map so that older links and handoffs can be interpreted correctly.

| Original phase | Integrated content | Endpoint |
| --- | --- | --- |
| 1 | Finite periodic compact SU(N) Wilson model, reflection positivity/OS carriers, genuine physical one-slab transfer and finite-volume spectral objects. | Existing finite-volume root |
| 2 | Normalized one-link laws, conditional expectation/L2 projection, deterministic and random-scan telescopes, fixed-volume covariance-remainder closure. | Existing covariance mechanics |
| 3 | Active-neighbor degree at most 18, base-L1 exponential weights, local Harnack and weighted Green/resolvent bounds. | #4560 |
| 4 | Actual response value set, least nonnegative supremum profile `R_can`, and pin-free dynamics/source forcing/terminal control. | #4583-#4595 |
| 5 | Aggregate remote family without target-cardinality loss, canonical remote column, local C5 exceptional-column control. | #4597-#4603 |
| 6 | Exact coefficient `M_can`, self-certificate, bootstrap, zero-coupling value, half-barrier exclusion and conditional continuation. | #4604-#4608 |
| 7 | Top-ray uniqueness, transfer/top-norm Lipschitz continuity, normalized real/complex transfer, fixed-z resolvent continuity and fixed-circle persistence. | #4609-#4613 |
| 8 | Fixed-contour Riesz operator `Q_beta` is norm-continuous and equals canonical `P_beta0` at the base point. | #4616 |
| 9 | Canonical complex top sector has rank one. | #4617 |
| 10 | Nearby bilateral absorption `Q_beta P_beta = P_beta = P_beta Q_beta`. | #4618 |
| 11 | Local radial resolvent margin, protected annulus, two-resolvent identity and contour deformation. | #4619 |
| 12 | Pinned-compatible nested-integral Fubini, exterior/interior Cauchy kernels, separated-circle integrability. | #4620-#4622 |
| 13 | Separated-circle double-resolvent identity; #4623 is superseded/unmerged, #4624 is the integrated version. | #4624 |
| 14 | Local fixed-contour idempotence `Q_beta^2 = Q_beta`, without assumed excited-gap continuity or nearby projector equality. | #4625 |

### Quantitative content retained from phases 2-6

For each fixed finite volume, the covariance remainder vanishes along complete random-scan blocks. This is not yet volume-uniform spatial covariance decay.

With `W_center(x) = s ^ baseL1Distance(center,x)`, the local weighted coefficient is

```text
rho_s = 18 * eta(beta) * s^2.
```

Local Green estimates are volume-independent under `rho_s < 1`. The actual profile satisfies the coarse bound `0 <= R_can(target,source) <= exp(16*beta)`. The pin-free response-controlled coefficient is

```text
c_pf(beta,s,M) = 18 * eta(beta) * s^2 + exp(16*beta) * M.
```

The aggregate remote-family theorem avoids a target-count factor; the local exceptional-column coefficient is `20 * s^2 * exp(16*beta) * eta_R(beta)`. The exact `M_can` is a finite source maximum, supplies its own canonical weighted-column certificate, satisfies a conditional bootstrap inequality, and has `M_can(0)=0`.

The half-barrier exclusion on the selected strictly positive volume-independent high-temperature interval is integrated. The implication from continuity to `M_can < 1/2`, and the reduction from `R_can` coordinate continuity to `M_can` continuity, are also integrated. At this checkpoint their final concrete continuity input is still to be connected.

## Phases 15-17 — Rank persistence, projector identification, moving continuity

**Status: CLOSED by [#4628](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4628) and [#4629](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4629).**

The norm-close-idempotent argument is now formal, not an informal inference from norm continuity:

```text
Q_beta^2 = Q_beta and ||Q_beta - P_beta0|| < 1
  -> P_beta0 restricted to range(Q_beta) is injective
  -> actual finite-dimensionality and range-dimension bound
  -> bilateral absorption of nonzero rank-one P_beta
  -> Q_beta = P_beta locally
  -> rank(Q_beta) = 1 locally
  -> beta -> P_beta is operator-norm continuous on Set.Ici 0.
```

Finite-dimensionality is established before numeric `finrank` comparison is used for range equality. Equal ranges alone do not identify two arbitrary projections; the proof uses the idempotence/absorption relations as well. No volume-uniform neighborhood or spectral-gap continuity is introduced.

## Phase 18 — The original canonical vacuum

### 18a. Existing L2 vector

**Status: CLOSED by [#4630](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4630).**

For fixed `H,N`, `N>0`, the existing nonnegative norm-one physical vacuum `Omega_beta` is norm-continuous on `beta>=0`; the same-root canonical complex embedding is continuous too.

The local identity is

```text
v_beta = P_beta^R Omega_beta0,
|v_beta| = ||v_beta|| * Omega_beta,
Omega_beta = |v_beta| / ||v_beta|| near beta0.
```

Nonvanishing is local around the base point. No global nonvanishing of the projection of one fixed reference vacuum is assumed, and no arbitrary sign/phase choice is left over.

### 18b. Existing continuous representative

**Status: CLOSED by [#4631](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4631).**

Kernel sections are curried while abstract, passed through `ContinuousMap.toLp` into fixed Haar L2, and paired with the existing norm-continuous vacuum. The resulting integral is identified with the original synthesis function. Division by the existing positive continuous top norm yields joint continuity of the original continuous representative.

The module additionally exports continuity into `C(X,R)` with its sup norm and joint continuity of the reciprocal. Both the raw kernel's all-real-coupling continuity and the vacuum's `beta=0` endpoint are covered. This is not pointwise evaluation of an arbitrary L2 class.

## Phase 19 — Actual fixed-right laws, literal responses, and the remaining supremum

### 19a. Generic normalized probability bridge

**Status: CLOSED by [#4632](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4632).**

For arbitrary topological parameter space `P`, compact integration space `X`, finite reference measure `mu`, jointly continuous nonnegative weight `w`, and strictly positive actual mass, the integrated generic endpoints are:

```text
continuous_integral_compact_domain
realIntegralWeightedDensity_joint_continuous
realIntegralWeightedProbabilityMeasure_integral_continuous
```

The last theorem uses the existing `realIntegralWeightedProbabilityMeasure`. Compactness belongs to the integration domain; no first-countability, metric, or local-compactness requirement on `P` is added. The actual denominator is retained rather than replaced by an assumed uniform floor.

### 19b. Actual ground-state kernel-section law

**Status: CLOSED by [#4633](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4633).**

With `w(beta,C,A) = Omega_cont(beta,A) * K(beta,A,C)` and `Z(beta,C) = integral w dHaar`, the original weight and normalized density `Z^(-1)*w` are jointly continuous. Jointly continuous tests have continuous expectations under the existing continuous-density law and the original L2-presented law, connected by exact equality of measures.

The proof uses the global Haar-a.e. identity only under full left-boundary integration. It does not infer its validity on every one-link fiber. The regression module also checks `beta=0` and reverse import order after the local-instance declaration-name collision was repaired.

### 19c. Literal target-ratio response

**Status: CLOSED by [#4634](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4634).**

The arbitrary-parameter expectation theorem permits extra continuously varying test parameters. A fixed-coordinate update is continuous in both its configuration and group value. The local factor is the quotient of the strictly positive updated/unupdated Wilson kernels by their established exact multiplication identity.

For fixed ordered `(target,source)`, both expectations use the same target-ratio observable, with the two right boundaries

```text
C_h = update (update B source h) target g2,
C_k = update (update B source k) target g2.
```

Subtracting these expectations and taking absolute value yields the literal `FixedRightTargetRatioResponseAbs`. The final exported endpoint is

```text
periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_joint_continuous
```

on `Set.Ici 0` times the full configuration/four-group-value space. Ordered pairs are unrestricted: `target=source` and `beta=0` are included. The new module also exports arbitrary-parameter original-law expectation continuity and response continuity.

Source: [implementation at the baseline](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/0bf8813960a5273da4348e4521b44c10bd20893d/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioResponseBetaContinuity.lean).

### 19d. Original canonical supremum profile

**Status: OPEN NOW — next coherent theorem unit.**

Keep the existing value set and canonical profile unchanged. At fixed finite `H,N,target,source`, package the test parameters as

```text
Theta = X x ((SU(N) x SU(N)) x (SU(N) x SU(N))),
f(beta,theta) = the literal ResponseAbs from #4634.
```

The required connection is:

1. establish the compact parameter-space instance and use the existing nonempty/bounded response-value facts;
2. prove exact equality between the original existential response value set and `f(beta) '' Set.univ` on `Theta`;
3. apply the pinned `IsCompact.continuous_sSup` to `isCompact_univ` and #4634's joint continuity;
4. transport through the original `max 0` definition to obtain coordinatewise `R_can` continuity on `Set.Ici 0`;
5. preserve the original target/source order and the zero-coupling endpoint in regression examples.

The required mathlib theorem exists in the [pinned `Mathlib/Topology/Order/Compact.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Order/Compact.lean#L477-L502). Availability of that theorem is not a substitute for formalizing the value-set identification and its application to the original `R_can`.

No new supremum profile, response majorant, continuity hypothesis, selected maximizer, or contraction estimate is needed upstream. Pointwise continuity with test parameters held fixed would be insufficient by itself; #4634 supplies the joint statement on the fixed compact domain.

### 19e. Exact canonical coefficient

**Status: conditional lift integrated in #4608; concrete application OPEN after 19d.**

Apply the existing finite weighted-sum/maximum continuity lift to all required `R_can` coordinates, retaining the exact canonical coefficient `M_can`. Do not redefine it or replace it by an auxiliary continuous envelope. Its additional weight parameters and interval hypotheses remain those in the existing theorem.

## Phase 20 — Actual half-barrier discharge

**Status: conditional theorem integrated in #4607; concrete discharge OPEN after 19e.**

Use the already established zero-coupling value and half-barrier exclusion with the newly supplied concrete continuity:

```text
M_can(0)=0 + continuity + M_can never equals 1/2
  -> M_can < 1/2 on the selected high-temperature interval.
```

Then use the existing coefficient estimates and their original weight/interval hypotheses to obtain strict `c_pf(beta,s,M_can) < 1`. Do not use a downstream physical gap, covariance decay, or sweep contraction to justify this continuity argument.

## Phases 21-27 — Downstream construction

| Phase | Required theorem unit | Boundary that remains |
| --- | --- | --- |
| 21 | Instantiate the actual pin-free kernel and derive strict weighted physical influence and source-to-target response/resolvent decay. | Strictness and the claimed constants must be uniform in periodic spatial volume. |
| 22 | Combine that decay with exact kernel-section covariance mechanics and fixed-volume remainder removal to obtain terminal base-L1 covariance decay. | A covariance identity or fixed-volume mixing theorem is not spatial decay. |
| 23 | Use cubic base-L1 shell summability to control the remote residual and close a strict physical sweep estimate. | The remote estimate is downstream of spatial decay; do not assume it to prove decay. |
| 24 | Convert physical response and conditional/block variance control into Poincare/coercivity on the actual physical carrier. | Keep the coercive constant uniform in volume. |
| 25 | Derive a positive transfer/Hamiltonian spectral bound uniform over the finite periodic volumes used in the limit. | Local finite-volume top isolation from the continuation proof is not this uniform theorem. |
| 26 | Construct compatible limiting states, same-root OS/Wightman carriers, limiting semigroup/Hamiltonian, and a sufficiently rich nontrivial four-dimensional gauge-field/state theory. | Auxiliary/scalar continuum lanes do not replace the intended physical construction. |
| 27 | Complete the intended four-dimensional Yang--Mills existence and mass-gap statement. | Still open at this repository checkpoint. |

A high-temperature finite-lattice continuation result alone does not establish the continuum regime or the necessary uniform limiting estimates. Each connection above must be separately proved on the correct carrier.

## Validation and reproducibility checkpoint

| Record | Exact value |
| --- | --- |
| Latest theorem PR | #4634, merged |
| Validated head | `6c4f22b0788abef884a5f0aaef360d2c3171d369` |
| Fast Check | #14711 / run `35694577932`, `completed/success` |
| Changed Lean job | `106638529081`, `completed/success` |
| Completion receipt job | `106639140412`, `completed/success` |
| Exact-head receipt | `chatgpt-ci-receipt/PR Lean Fast Check`, `success` |
| Theorem merge | `0bf8813960a5273da4348e4521b44c10bd20893d` |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

[CI run](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/35694577932) validation covers the changed implementation, its four regression examples, and their dependency closure. It is not a fresh whole-repository aggregate build. The successful fallback build after a missing cached new `.olean` is distinct from the first direct-check diagnostic; a workflow receipt does not mean every cached dependency was freshly rebuilt.

The #4634 regression examples cover arbitrary-parameter expectations under the original law, arbitrary-parameter literal response, the full joint product domain, and `beta=0` with coincident target/source. Recent fixes retain theorem propositions and use explicit half-line membership, typed projections, pinned `Function.update_self` / `Function.update_of_ne`, uniquely named local instances, and abstract opaque theorem boundaries instead of expanding large concrete vacuum terms. Heartbeat budgets remain `500000` / `synthInstance 50000` for the concrete module.

## Immediate continuation checklist

```text
1. Fresh-read the theorem branch; distinguish docs-only pointer updates.
2. Consume #4634's literal joint ResponseAbs theorem.
3. Identify the original response value set with the compact image.
4. Prove original R_can coordinate continuity, including beta=0.
5. Apply #4608 to the actual M_can, preserving all weight parameters.
6. Apply #4607 on its original interval; discharge the half barrier.
7. Enter strict weighted physical influence and spatial decay.
8. Continue covariance -> remote residual -> coercivity -> uniform gap
   before promoting any thermodynamic/continuum conclusion.
```

## Permanent semantic boundaries

```text
fixed-volume theorem != volume-uniform estimate != continuum theorem
local contour continuity requires an identification before it becomes canonical projector continuity
range equality alone != operator equality for arbitrary projections
L2 classes cannot be evaluated pointwise without a justified representative
full-boundary Haar-a.e. equality cannot be restricted to arbitrary fibers
continuous-test expectation continuity != a separate total-variation theorem
joint literal response continuity still requires the original supremum connection
half-barrier exclusion still requires continuity for strict sub-barrier continuation
fixed-volume ergodicity != spatial covariance decay
covariance identities != decay != physical coercivity != mass gap
```

The projector/vacuum/law/response bridges are integrated where explicitly marked above. The remaining boundaries specify the hypotheses of future theorem applications, not reasons to restart completed work or replace the intended Yang--Mills construction with a weaker target.
