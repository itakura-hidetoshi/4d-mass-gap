# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. Its integrated finite-volume development includes periodic Wilson lattice gauge theory, Osterwalder--Schrader carriers, physical transfer operators, conditional expectation, quantitative spatial response, and canonical-vacuum continuation.

**Current endpoint — 2026-09-22 JST:** the literal fixed-right target-ratio response is jointly continuous in the nonnegative coupling, boundary configuration, and all four group-valued test parameters. This uses the existing canonical vacuum and probability laws, not newly selected substitutes. The theorem is integrated through [PR #4634](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4634).

**Next theorem unit:** pass from this joint continuity to the unchanged canonical supremum profile `R_can`, then apply the existing coordinate-to-`M_can` and half-barrier continuation theorems.

> **Claim boundary.** This repository does not yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem. The new results concern fixed finite volume. Canonical-response supremum continuity, its strict high-temperature consequence, volume-uniform physical coercivity, and the thermodynamic/continuum construction remain separately tracked obligations. The detailed development order is in [ROADMAP.md](ROADMAP.md).

## Repository authority

| Item | Authoritative value for this refresh |
| --- | --- |
| Theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Theorem-bearing mathematical baseline | `0bf8813960a5273da4348e4521b44c10bd20893d` |
| Baseline theorem PR | #4634 — joint continuity of the literal fixed-right target-ratio response |
| Validated PR head | `6c4f22b0788abef884a5f0aaef360d2c3171d369` |
| Public landing/documentation branch | `main` — not theorem authority |

The baseline is the [#4634 merge commit](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/0bf8813960a5273da4348e4521b44c10bd20893d), not its tested PR head. Later documentation-only commits advance a branch pointer without changing the mathematical baseline. Synchronizing these two documents to `main` does not synchronize the theorem tree or promote `main` to theorem authority.

Authority order is: exact current GitHub theorem-carrier SHA; formal Lean artifacts; README/ROADMAP; CI/runtime receipts; historical summaries or memory. Re-observe the [theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) before continuing work; this document records a checkpoint, not a permanently current branch pointer.

## Proof spine at a glance

```text
FINITE WILSON / OS / PHYSICAL TRANSFER ROOT                  integrated
  -> exact one-link laws and conditional expectations
  -> fixed-volume covariance-remainder closure
  -> volume-independent local weighted Harnack theory

CANONICAL RESPONSE / BOOTSTRAP ARCHITECTURE                  #4583-#4608
  -> actual supremum profile R_can and pin-free recurrence
  -> aggregate remote family and local C5 exceptional column
  -> exact coefficient M_can, self-certificate, M_can(0)=0
  -> half-barrier exclusion and conditional continuity lift

SPECTRAL CONTINUATION TO THE EXISTING VACUUM                 #4609-#4631
  -> transfer/resolvent continuity and fixed Riesz contour
  -> contour idempotence, rank persistence, Q_beta = P_beta
  -> moving canonical projector norm-continuity
  -> existing nonnegative normalized vacuum L2-continuity
  -> existing continuous representative joint/sup-norm continuity

ACTUAL FIXED-RIGHT LAW AND RESPONSE                         #4632-#4634
  -> compact-domain normalized expectation continuity
  -> actual kernel-section density and law expectations
  -> literal target-ratio ResponseAbs joint continuity

CURRENT FRONTIER                                           not yet integrated
  -> identify the original response value set as a compact image
  -> R_can coordinate continuity via compact supremum
  -> M_can continuity via #4608
  -> actual high-temperature half-barrier bound via #4607

DOWNSTREAM                                                 open
  -> strict weighted physical influence and spatial decay
  -> terminal covariance decay / uniform remote residual
  -> physical sweep contraction / Poincare / coercivity
  -> uniform finite-volume transfer/Hamiltonian gap
  -> compatible thermodynamic and continuum physical construction
```

## What changed since the fixed-contour checkpoint

The previous documentation stopped at #4625. Its projector, vacuum, and kernel-law continuity tasks are no longer the immediate frontier.

| Integrated PR | Mathematical contribution |
| --- | --- |
| [#4628](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4628) | Norm-close idempotent range injection and rank comparison. |
| [#4629](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4629) | Finite-dimensional range control, nearby `Q_beta = P_beta`, exact local rank one, and moving canonical CFC projector norm-continuity. |
| [#4630](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4630) | Norm-continuity of the already defined nonnegative unit physical vacuum in real L2 and its canonical complex embedding. |
| [#4631](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4631) | Joint continuity of the original continuous vacuum representative, continuity into `C(X, R)` with its sup norm, and reciprocal continuity. |
| [#4632](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4632) | Generic compact-domain continuity of integrals, actual normalized densities, and expectations under the existing weighted probability measure. |
| [#4633](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4633) | Joint continuity of the actual fixed-right weight/density and continuous-test expectations, including the original L2-presented law. |
| [#4634](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4634) | Arbitrary-parameter expectation transport, local-factor continuity, and joint continuity of the literal target-ratio response. |

### 1. From a fixed contour to the canonical vacuum

At fixed finite volume, let `Q_beta` be the continuation along the contour fixed at `beta0`, and let `P_beta` be the moving canonical complex CFC top projector. The earlier contour calculus proves continuity of `Q_beta`, local idempotence, and bilateral absorption of `P_beta`.

PRs #4628-#4629 complete the missing identification. A strict bound `||Q_beta - P_beta0|| < 1` makes the restriction of `P_beta0` to `range(Q_beta)` injective. Actual finite-dimensionality is established before using finite-dimensional range comparison. Idempotence and bilateral absorption then give operator equality `Q_beta = P_beta`; equality of ranges alone is not substituted for equality of operators.

PR #4630 proves continuity of the existing nonnegative normalized vacuum `Omega_beta`, rather than selecting another continuous vector. Locally around `beta0`, it uses

```text
v_beta = P_beta^R Omega_beta0,
Omega_beta = |v_beta| / ||v_beta||.
```

Only local nonvanishing of `v_beta` is needed. The physical L2 absolute-value operation removes the sign ambiguity, and the original canonical normalization is retained.

PR #4631 pairs the L2 vacuum with continuous kernel sections through mathlib's continuous linear map `ContinuousMap.toLp`, identifies the scalar integral with the existing synthesis function, and divides by the positive continuous top norm. The result is joint continuity of the original representative `Omega_cont(beta,A)`, its sup-norm continuity on the compact boundary, and joint continuity of its reciprocal. It does not evaluate an arbitrary L2 equivalence class pointwise.

### 2. The actual normalized fixed-right law

Write `X` for the finite boundary configuration space, `mu` for its Haar measure, and `C` for the fixed right boundary. The existing continuous weight and its actual mass are

```text
w(beta,C,A) = Omega_cont(beta,A) * K(beta,A,C),
Z(beta,C)   = integral_A w(beta,C,A) dmu(A) > 0.
```

PRs #4632-#4633 prove joint continuity of `w` and `Z^(-1) * w`, and continuity of

```text
(beta,C) -> integral_A f(beta,C,A) dnu_beta,C(A)
```

for jointly continuous real tests `f`. Here `nu_beta,C` is the existing probability law. Its continuous-density and original L2 presentations are connected by the already established exact measure equality. Positivity of the actual mass is supplied by the model, not an additional uniform lower-bound hypothesis.

The global Haar-a.e. identity is used under full left-boundary integration only. It is not restricted to an arbitrary one-link fiber. These are density and expectation theorems; a separate total-variation or measure-topology theorem is not asserted here.

### 3. The literal response is jointly continuous

For fixed ordered links `(target,source)`, define the shorthand

```text
D_beta(B,g1,g2,h,k) = existing FixedRightTargetRatioResponseAbs.
```

PR #4634 proves joint continuity on

```text
[0,infinity) x (X x ((SU(N) x SU(N)) x (SU(N) x SU(N)))).
```

The theorem includes `beta=0` and `target=source`. It also exports an arbitrary-topological-parameter version, allowing the coupling, configuration, and four test values to vary continuously together.

The local factor is recovered from the exact positive Wilson-kernel update identity as a quotient of updated and unupdated kernels. The same target-ratio observable is integrated against the two updated-boundary laws; subtraction and absolute value give the original response. Neither a surrogate response nor an assumed response-continuity certificate is used.

The [implementation](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/0bf8813960a5273da4348e4521b44c10bd20893d/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioResponseBetaContinuity.lean) and [four regression examples](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/0bf8813960a5273da4348e4521b44c10bd20893d/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioResponseBetaContinuityCompileSmoke.lean) are available at the exact baseline.

## Immediate next step: the canonical supremum, not another vacuum construction

The existing definition is

```text
R_can(beta,target,source)
  = max 0 (sSup {D_beta(B,g1,g2,h,k) | B,g1,g2,h,k}).
```

It must remain the same definition. The next proof should identify its existing value set with the image of the compact configuration/four-group-value domain, apply the pinned mathlib `IsCompact.continuous_sSup` theorem to #4634, and transport the result through `max 0`.

This compact-supremum application is the next repository theorem obligation; #4634 itself does not yet assert `R_can` continuity. Once it is integrated, the existing [#4608](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4608) lift supplies continuity of the exact finite coefficient `M_can`. The already proved `M_can(0)=0` and half-barrier exclusion then feed [#4607](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4607) on its specified high-temperature interval.

The generic implication is integrated, but its model-facing continuity premise has not yet been discharged at this checkpoint:

```text
R_can coordinate continuity
  -> M_can continuity
  -> M_can < 1/2 on the selected high-temperature interval
  -> strict canonical pin-free weighted coefficient.
```

## Earlier integrated quantitative structure

The continuation work serves an existing response-controlled program; it does not replace it. That program includes the canonical profile's nonnegativity, minimality, and coarse bound `R_can <= exp(16*beta)`; pin-free finite-step/source-forcing recurrences; fixed-volume terminal removal; aggregate remote-family closure without target-cardinality loss; and the local C5 exceptional-column estimate.

The sparse local weighted coefficient is `rho_s = 18 * eta(beta) * s^2`. The pin-free coefficient is

```text
c_pf(beta,s,M) = 18 * eta(beta) * s^2 + exp(16*beta) * M.
```

The exact canonical `M_can` supplies its own weighted-column certificate and a conditional bootstrap bound. These formulas and local estimates are not, by themselves, the downstream strict spatial-decay or physical-coercivity theorem.

## Downstream construction obligations

After the actual continuity/half-barrier connection, the program must separately derive strict weighted physical influence, source-to-target spatial response decay, terminal base-L1 covariance decay, cubic-shell summability, and a volume-uniform remote residual. The subsequent physical sweep contraction, Poincare/coercivity estimate, uniform finite-volume transfer/Hamiltonian gap, and compatible thermodynamic/continuum physical construction are still distinct stages.

A fixed-volume isolated top eigenvalue is not a volume-uniform gap. A uniform finite-volume estimate is not automatically a continuum Yang--Mills field construction. Auxiliary or scalar continuum lanes do not replace the sufficiently rich same-root OS/Wightman physical carrier required at the end.

## Toolchain and verification

The exact baseline uses `leanprover/lean4:v4.30.0-rc2` and mathlib revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. The repository lockfiles, not newer online API signatures, control compilation.

For #4634, [PR Lean Fast Check #14711 / run 35694577932](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/35694577932) is `completed/success` on head `6c4f22b0788abef884a5f0aaef360d2c3171d369`. The changed-Lean job, completion-receipt job, and exact-head `chatgpt-ci-receipt/PR Lean Fast Check` status succeeded. This records validation of the changed modules and their dependency closure, not a fresh whole-repository aggregate build or a new theorem verification by a later docs-only CI run.

Recent proof engineering uses uniquely named local instances to avoid cross-import declaration collisions, explicit product/projection types, pinned `Function.update_self` / `Function.update_of_ne`, and abstract private proof boundaries to avoid repeated expansion of concrete Wilson/vacuum definitions. The mathematical hypotheses and heartbeat budgets were not weakened or enlarged to obtain #4634's success.

## Permanent distinctions

```text
finite-volume continuity != volume-uniform estimates
L2 vacuum continuity != point evaluation of an arbitrary L2 representative
continuous-test expectations != an asserted total-variation theorem
literal response joint continuity != the completed R_can supremum connection
M_can != 1/2 does not imply M_can < 1/2 without continuation
fixed-volume mixing != spatial covariance decay
covariance identities != covariance decay != mass gap
uniform finite-volume gap != continuum Yang--Mills construction
```

The earlier fixed-contour/moving-projector distinction has been bridged by #4629, not ignored. Likewise, #4630-#4634 close specific vacuum/law/response connections without collapsing the later layers. No `sorry`, `admit`, new axioms, hidden constants, or weakened statements are substitutes for the remaining proofs.
