# MGAP4D

Formal Lean/mathlib development for the four-dimensional Yang--Mills mass-gap program.

The current formal theorem carrier is **not** the GitHub default branch.  All
mathematical status statements in this README are relative to the authoritative
branch and exact commit recorded below.

## Current status — 2026-09-29 JST

Repository:

`itakura-hidetoshi/4d-mass-gap`

Authoritative theorem-carrier branch:

`formal/real-hilbert-uniform-coercive-strong-limit`

Current theorem-bearing HEAD:

`696fd06775636f31f0364e331103a009cc729fde`

This is the merge commit of PR #4899.

Pinned formal environment:

- Lean `v4.30.0-rc2`
- mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

The GitHub default branch `main` is **not** theorem authority.

## Claim boundary

This repository contains a large formal construction spine for finite-volume
Wilson / Osterwalder--Schrader / physical-transfer Yang--Mills structures,
together with an exact beta-zero gap result and a growing positive-beta
response/Schur analysis.

It does **not** currently constitute a complete formal proof of the continuum
four-dimensional Yang--Mills existence and mass-gap problem.

The active missing step is still in the finite-volume positive-beta physical
gap route.  In particular, the recent PRs #4892--#4899 isolate the exact
noncommutative sweep obstruction and put its terminal second-sweep carrier into
the existing response/Schur framework, but the final semantic source-update
inequality and a strict quantitative next-defect contraction are not yet
closed.

## Core notation at the current frontier

For one spatial color `c`, write:

- `B_c` for the genuine color-block conditional-expectation projection;
- `S_c` for one complete canonical same-color one-link sweep;
- `L_c(f)` for the exact one-pass sweep path loss;
- `D_c(f) = ||S_c f - B_c f||^2` for the sweep--block defect energy.

At beta zero, same-color one-link projections commute and

```text
S_c = B_c
```

exactly.  Hence the sweep--block defect vanishes at beta zero.

At positive beta, commutativity is **not** assumed.  The defect is the precise
one-pass non-idempotence obstruction.

## Exact renewal / cyclic carrier now closed

PR #4892 proves the fixed-color energy renewal

```text
D_c(f) = L_c(S_c f) + D_c(S_c f).
```

PR #4893 exposes the vector identity behind it:

```text
defectVector_c(f)
  = residualVectorSum_c(S_c f)
    + defectVector_c(S_c f).
```

For a canonical split

```text
canonicalList = pre ++ e :: suffix
```

PR #4894 proves that the operators acting between the first and second visits
to target `e` occur in the exact cyclic order

```text
suffix ++ pre.
```

Equivalently, the second-sweep `e)-stage residual is the target-`e`
residual obtained after propagating the first post-`e` vector through this
cyclic between-visits order.

PR #4895 then proves that the same cyclic second-visit state admits the bounded
strongly measurable concrete representative required by the physical
source-update / response machinery.  No carrier identification is implicit:
the representative equality is formalized in the genuine ground-state joint
L2 space.

## Terminal profile and response energy

PR #4896 introduces the link-indexed terminal second-sweep profile

```text
terminalProfile(e)
```

and proves the exact normalization

```text
(1/6) * sum_e terminalProfile(e)^2
  = terminalSweepPathLoss(f),
```

where

```text
terminalSweepPathLoss(f)
  = (1/6) * sum_c L_c(S_c f).
```

It also proves the six-color averaged renewal

```text
defectMean(f)
  = terminalSweepPathLoss(f)
    + nextDefectMean(f).
```

PR #4897 factors out a generic coefficient-one profile-to-variance bridge and
feeds the PR #4895 cyclic representatives into the existing response-energy
machinery.  On the existing response cutoff:

```text
terminalResponseEnergy
  <= rhoResp(s,beta) * ofReal(6 * terminalSweepPathLoss(f)).
```

The already-closed response coefficient satisfies a volume-independent strict
cutoff with

```text
rhoResp(s,beta) < 1
```

on its certified positive-beta interval, and `rhoResp(s,0) = 0`.

## Terminal-profile Schur receiver

PR #4898 specializes the existing transpose Schur receiver to the terminal
profile.

If the remaining semantic one-sided relation

```text
terminal(source)
  <= originalLocal(source)
     + sum_target K(target,source) * terminal(target)
```

is supplied, then

```text
(1 - q_phys(s,beta))^2 * terminalSweepPathLoss(f)
  <= originalSweepPathLoss(f).
```

The same PR packages the averaged renewal receiver:

if

```text
nextDefectMean(f) <= rho * defectMean(f),
```

then

```text
(1 - rho) * defectMean(f)
  <= terminalSweepPathLoss(f).
```

Combining the two premises gives the coefficient-preserving form

```text
(1 - q_phys)^2 * ((1 - rho) * defectMean(f))
  <= originalSweepPathLoss(f).
```

No division by `1-q_phys` or `1-rho` is performed before strict positivity
is certified.

This is a receiver, not yet the final positive-beta defect margin.  In
particular, a coefficient-one local term by itself is not enough to conclude
the required small bound `delta(beta) < 1/6`; the semantic estimate must
retain the beta-small structure needed near the exact beta-zero endpoint.

## Exact cyclic source set

PR #4899 closes the finite geometry of the between-visits order.

For

```text
canonicalList = pre ++ e :: suffix
```

with the preserved freshness witness,

```text
d ∈ suffix ++ pre  <->  d != e
```

inside the fixed-color fiber, and

```text
(suffix ++ pre).toFinset = Finset.univ.erase e.
```

Thus the cyclic source list contains exactly every other link in the same
spatial-color class.  Every source passed to the direct/backward/transposed
response machinery is therefore formally off-diagonal from target `e`,
without source reordering or a cardinality estimate.

## Closed response / direct assets reused by the frontier

The current route reuses, rather than rebuilds, the following closed pieces.

### Response / RMS side

- target-law response L2 realization;
- first-cross exact Pythagorean split;
- Harnack transport and stationarity return;
- genuine target residual / canonical fiber variance;
- fixed-background response Fubini;
- configuration-independent bidirectional pin-free Schur bounds;
- canonical sweep representatives;
- exact stage residual energy = sweep path loss;
- strict positive response cutoff `rhoResp < 1`;
- physical full-minus-direct finite-update error control.

### Direct / backward side

- exact `DirectDifferenceL2` energy realization;
- coefficient-one direct L2 to ordered direct-average comparison;
- lossless ordered-to-backward reversible-carrier transport;
- exact backward direct variance + mean-square Pythagorean split;
- backward centered-variance transport to the genuine source residual;
- current-value reference reanchoring;
- exact backward law-response = negative transposed canonical response;
- backward law-response energy = transposed response L2 energy;
- transposed law-response bound with orientation
  `K_pin(source,target)`.

## Beta-zero endpoint

The beta-zero endpoint remains stronger than the perturbative receiver.

Closed exact result:

```text
physical transfer gap at beta = 0 = 1.
```

The later defect-margin receiver also yields a weaker beta-zero lower bound
when `delta(0)=0`.  That perturbative lower bound must not be confused with
the exact beta-zero gap.

## Current mathematical frontier

After PR #4899, the immediate target is no longer list geometry or carrier
identification.  Those are closed.

The next theorem unit should connect the actual cyclic source updates in
`suffix ++ pre` to the terminal target residual while preserving the exact
source/target orientation.

The desired semantic shape is a volume-uniform one-sided terminal-profile
estimate, refined enough to retain beta-smallness near beta zero.  Schematically:

```text
terminalProfile(source)
  <= smallLocal(beta) * originalProfile(source)
     + sum_target K(target,source) * terminalProfile(target).
```

The exact coefficient and carrier must come from the already-formalized
direct/backward/law-response decomposition; it should not be inserted by a
finite-cardinality Cauchy estimate or an arbitrary factor two.

A second required quantitative ingredient is a strict next-defect contraction
(or an equivalent lower bound on terminal path loss):

```text
nextDefectMean(f) <= rhoDefect(beta) * defectMean(f),
rhoDefect(beta) < 1.
```

Once these are closed, the route is:

```text
cyclic semantic estimate
  -> terminal-profile Schur feedback
  -> strict renewal contraction
  -> defectMean(f) <= delta(beta) * ||f||^2
  -> certify delta(beta) < 1/6
  -> existing full-sweep transfer-gap receiver
  -> positive finite-volume physical transfer gap.
```

Only after the finite-volume volume-uniform gap is closed should the
thermodynamic / continuum OS--Wightman part be advanced as the active
frontier.

## Recent theorem-bearing sequence

| PR | Merge commit | Role |
| --- | --- | --- |
| #4892 | `2727e50414cd2f6373a2fbde89ab3c71a47e3672` | exact defect renewal |
| #4893 | `847e21e62321f4061f1945455bb17977f687409b` | vector renewal |
| #4894 | `551fe25176f2d723dcc54c80f2fda723fece57fd` | cyclic second-visit identity |
| #4895 | `1bacd3da86db26027ba5ade88a837b4ff7331bd6` | bounded cyclic representatives |
| #4896 | `866770a7215a9a1564d2416e41f177857f4e98ae` | terminal profile + averaged renewal |
| #4897 | `6091310e11647fd19b523abfc93f97578fa0a81d` | terminal response energy |
| #4898 | `f67a2afdc7083aef9218b6dc2ec8c31d72ec1dac` | terminal-profile Schur feedback receiver |
| #4899 | `696fd06775636f31f0364e331103a009cc729fde` | exact cyclic source set |

## Status summary

```text
finite Wilson / OS / physical-transfer root                    CLOSED
exact beta-zero physical transfer gap = 1                      CLOSED
positive-beta response / RMS / bidirectional Schur side        CLOSED
canonical prefix / vector telescoping / stage residual spine    CLOSED
physical full = direct + response L2 decomposition              CLOSED
direct L2 -> backward variance / law-response transport         CLOSED
sweep-block terminal geometry and exact renewal                 CLOSED
cyclic second-visit order                                       CLOSED
bounded cyclic second-visit representatives                     CLOSED
terminal profile / six-color renewal                            CLOSED
terminal response energy -> terminal path loss                  CLOSED
terminal-profile Schur feedback receiver                        CLOSED
cyclic between-visits source set = all other same-color links   CLOSED

cyclic source-update semantic one-sided estimate                OPEN
beta-small quantitative coefficient closure                    OPEN
strict next-defect contraction                                  OPEN
delta(beta) < 1/6                                               OPEN
positive-beta finite-volume physical transfer gap               OPEN
thermodynamic / infinite-volume construction                    OPEN
continuum OS / Wightman construction                            OPEN
continuum Yang--Mills mass gap                                  OPEN
```

## Lean / mathlib engineering discipline

- Always fresh re-observe the theorem-carrier branch before creating or
  classifying a theorem PR.
- Judge CI only at the exact current PR head SHA.
- The theorem-bearing GREEN criterion is the completed
  `PR Lean Fast Check` plus the exact-head
  `chatgpt-ci-receipt/PR Lean Fast Check` success receipt.
- Do not rerun Strict Lean merely because a theorem-bearing PR already passed
  the required exact-head Fast Check.
- Docs-only updates do not require Strict Lean.
- On RED, inspect the full changed Lean module, CompileSmoke, imports,
  dependent theorem signatures, typeclass instances, and pinned mathlib APIs.
- Prefer compact local aliases and explicit `calc` blocks over giant
  dependent `rw` / `unfold` chains.
- Preserve `K_pin(source,target)` or `K(target,source)` exactly as specified
  by the theorem being applied.  Never infer response symmetry.
- Do not introduce finite-cardinality Cauchy losses, arbitrary factors two, or
  volume-dependent multiplicities.
- Do not pointwise-evaluate arbitrary L2 quotient representatives.
- Do not identify measure-indexed carriers without an explicit equality,
  isometry, cast, or proved transport theorem.
- Do not assume positive-beta one-link projections commute.

## Navigation

- `ROADMAP.md` — exact current proof frontier and restart sequence.
- `MGAP4D/MathlibAnalytic` — formal analytic theorem development.
- authoritative theorem-carrier —
  `formal/real-hilbert-uniform-coercive-strong-limit`.
