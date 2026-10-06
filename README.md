# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Theorem snapshot: 2026-10-06 JST, through merged [PR #5212](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5212).**

The current advance is an exact connection between **literal posterior fiber integrals**, **finite ordered updates**, and **the existing ground-state joint L2 conditional-expectation projections**. The latest theorem identifies each literal stage-residual energy with the corresponding projection norm loss. The next model-facing task is to construct the quantitative residual majorants that this identity can consume.

A complete continuum Yang--Mills construction, a nontrivial physical-time Hamiltonian, and a Wightman / energy-momentum mass-gap theorem are **not established by this checkpoint**. Finite-volume identities, conditional convergence theorems, and physical-time existence are kept separate below.

## 1. Authority and reproducibility

| Item | Value at this documentation checkpoint |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing baseline | `c5e283ff596cfe00e2bb8ebf8fc92d1938b749a5` |
| Latest theorem-bearing PR | #5212, merged |
| Validated #5212 PR head | `014856b9cd02a56670beb891c1bb5b6895c26a4e` |
| Exact-head Lean Fast Check | [run 37434311434](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37434311434), completed / success |
| Changed Lean job / receipt publisher | `112172256508` / `112173652910`, both success |
| Exact-head commit receipt | `chatgpt-ci-receipt/PR Lean Fast Check`: success |
| Pinned Lean | `v4.30.0-rc2` |
| Pinned mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

The default branch **`main` is not theorem authority**. A later documentation-only merge can move the theorem-carrier branch without replacing the theorem-bearing baseline above. Re-observe the branch before continuing; do not treat a README snapshot as a live branch ref.

Authority order: fresh exact theorem-carrier SHA; formal Lean artifacts at that SHA; README / ROADMAP; matching exact-head CI receipts; conversation history. The [ROADMAP](ROADMAP.md) gives the implementation order, remaining hypotheses, and source entry points.

## 2. What is closed, and at what scope?

| Layer | Status and qualification |
| --- | --- |
| Finite-volume quantitative transfer lane | Retained: `kappa_12 >= 1/2304`, physical transfer-gap floor `>= 1/3072`, and `q0 = 3071/3072`, under the existing finite-volume theorem hypotheses. The non-top power receiver includes the completed physical pair sector. This is not an unrestricted statement for every coupling or a physical continuum mass. |
| H1-D4 and the old H1-D5 route | H1-D4 fixed-space identification is proved. The old completed H1-D5 compatibility is refuted at positive SU(2) coupling; it is not a pending assumption to restore. |
| Adjacent-scale continuum-existence reductions | Finite reconstruction, projection-variance identities, explicit same-volume beta response, and fixed-natural-time Cauchy/strong-limit implications are available. Their quantitative adjacent-scale inputs remain to be supplied. |
| Actual posterior locality | Canonical response / Dobrushin infrastructure and local-factor spatial covariance decay are available on their stated high-temperature intervals. This is not yet the full six-spatial stage-profile tail. |
| Posterior / genuine joint connection | #5208--#5212 identify fiber laws, joint-a.e. means, bounded-core CondExpL2 action, arbitrary finite ordered schedules, and literal stage-residual energy. |
| Posterior finite-mass scaling certificate | #5207 proves that the existing certificate confined to the canonical closed strict-Dobrushin interval has no inhabitants. |
| Physical continuum dynamics | Actual H1-C3 quantitative closure, a compatible limiting transfer operator, spacing-sensitive H2 dynamics, and H3/H4 reconstruction remain separate obligations. |

The recent exact joint identities hold for **any natural H, N > 0, and beta >= 0**, with the observable hypotheses in their declarations. The three-mode adjacent-refinement route and the positive-coupling H1-D5 counterexample are **SU(2)-specific**. These scopes must not be silently exchanged.

## 3. The new exact chain: fiber law to stage energy

Let `muJ` be the existing genuine ground-state joint probability law, `z = (L,R)` a boundary pair, and `e` a right spatial link. Write the literal posterior update as

```text
(M_e F)(L,R)
  = integral F(L, R[e <- g]) d nuPost_(L,R,e)(g).
```

### Fiber normalization and joint-a.e. identification: #5208--#5209

A positive scalar cancels exactly from a normalized exponential weight:

```text
Doob(mu, c * exp(f)) = mu.tilted(f),  c > 0,
```

with the stated integrability and nonzero-measure hypotheses. In the model, the canceled factor is `||T_phys||^(-1) * Omega_cont(L) > 0`.

This identifies the continuous-compatible fiber law pointwise. The historical L2-vacuum fiber law is identified first on Haar-a.e. left/off-target contexts and then **muJ-almost everywhere**. The common full-measure event for fiber-law and arbitrary-test mean identities does not depend on the test function. No equality on exceptional fixed fibers is asserted.

Sources: [fiber normalization](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberPosteriorMeasureBridge.lean), [joint-a.e. transport](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberPosteriorJointAEBridge.lean).

### Existing joint CondExpL2 action: #5210

For a bounded strongly measurable real function F on both boundaries,

```text
[M_e F]_(L2(muJ)) = P_e [F]_(L2(muJ)),
```

where `P_e` is the pre-existing genuine joint conditional-expectation projection. The literal formula has MemLp 2 and defines that same vector in the original Hilbert carrier. A corollary uses the existing right-boundary bounded-continuous-function interface.

The earlier arbitrary-test change-of-variables identity uses the totalized Bochner integral; it does not itself assert integrability. The L2 theorem retains its bounded strongly measurable core.

Source: [posterior / CondExpL2 identification](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointCondExpIdentification.lean).

### Finite chronological schedules: #5211

Joint-a.e. equality of observables is preserved by canonical and literal posterior means. This supplies the missing justification for replacing an intermediate function inside the next fiber integral.

For any finite list `[e1, ..., em]`, with the first listed map acting first,

```text
[M_em ... M_e1 F]_(L2(muJ)) = P_em ... P_e1 [F]_(L2(muJ)).
```

Empty lists and repeated links are allowed. The specified order is preserved; different projections are not assumed to commute. Canonical intermediates remain strongly measurable with the same pointwise bound. The projection product is the existing `realHilbertProjectionSweep`, not a new operator family.

Source: [finite schedules](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointFiniteSchedule.lean).

### Literal stage-residual energy: #5212

For a finite prefix `pre`, next target e, and `G = M_pre F`, put

```text
r_(pre,e) = G - M_e G,
x = [G]_(L2(muJ)).
```

The residual belongs to L2, its square is integrable, and

```text
integral r_(pre,e)^2 d muJ
  = ||x - P_e x||^2
  = ||x||^2 - ||P_e x||^2.
```

An a.e. majorant `|r_(pre,e)| <= |b|`, with `b` in L2, therefore gives

```text
||x - P_e x||^2 <= integral b^2 d muJ.
```

A constant bound `|r_(pre,e)| <= delta`, `delta >= 0`, gives exactly `delta^2` under the original probability law. **The majorant is an explicit input, not a newly constructed spatial decay estimate.** The identity introduces no extra density-comparison coefficient.

Successive norm losses telescope. Do not replace their sum by the squared total vector defect for noncommuting projections.

Source: [stage residual and energy](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointStageResidualEnergy.lean).

## 4. Locality is available, but the stage-profile bridge is still the next task

[PR #5199](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5199) proves, for the specified posterior local factors at a plaquette-remote ordered pair,

```text
|Cov_post(L_target, L_source)| <= C(s,beta) / s^d_baseL1(source,target).
```

The prefactor is independent of H and N on the canonical half-barrier interval. The theorem permits `s >= 1`; a genuinely decaying exponential requires `s > 1`. The strict uniform-Dobrushin coefficient uses its own cutoff with `s > 8`. Preserve the particular theorem's cutoff and separation hypotheses when composing results.

Source: [actual local-factor covariance decay](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalSpatialCovarianceDecay.lean).

The immediate construction is now:

```text
actual posterior link-variation bounds at the exact finite prefixes
  -> literal residual majorants, with the required fiber regularity
  -> #5212 coefficient-one stage-energy bounds
  -> exact fixed-color prefix / six-spatial profile alignment
  -> continuous scalar majorant on the bounded-continuous dense core
  -> #5147 / #5148 closure at the actual frozen Krylov vector.
```

Local-factor covariance decay alone is not this theorem. The dense-core receiver requires a continuous final scalar majorant, not L2-continuity of every pointwise oscillation coordinate, and does not give every L2 vector a bounded-continuous representative.

## 5. Two no-go results that must remain visible

### Old completed H1-D5 compatibility

At positive SU(2) coupling, the old completed cross-scale compatibility forces a rank-one behavior incompatible with the constructed two-mode sector. Do not reintroduce vacuum/top alignment, equivalent whole-operator descent, or an OS/physical-transfer equality by changing the name of the assumption.

### #5207: the strict-interval posterior scaling certificate is empty

For fixed `s > 8`, the canonical full-sweep factor is

```text
rho(s,beta) = exp(-(1 - alphaBar(s,beta))).
```

The old generator-scaling certificate requires `a_n > 0`, `a_n -> 0`, every `beta_n` in the canonical **closed** interval `[0, beta_cut(s)]`, and

```text
(1 - alphaBar(s,beta_n)) / a_n -> m,  0 < m < infinity.
```

Finite scaling forces `alphaBar(s,beta_n) -> 1`. Continuity on the compact interval gives a cluster-point value equal to 1, contradicting the existing strict coefficient bound there. The certificate type is therefore empty.

The conditional implications introduced before #5207 remain valid implications, but their certificate is **not an available construction target inside that interval**. This does not refute every continuum route, produce a critical coupling outside the interval, or identify posterior update count with Euclidean time.

Source: [strict-interval no-go](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFiniteMassUniformDobrushinNoGo.lean).

## 6. Remaining continuum obligations

The SU(2) adjacent-refinement target still includes

```text
V_(n,r,k) = ||Y_(n,r,k) - P_n^phys Y_(n,r,k)||^2.
```

The existing reductions split the work into a locality/profile contribution, a **separate common-marginal physicality defect**, a vector-wise physical transfer/reconstruction commutation tail, and explicit weighted beta increments. None is automatically discharged by the posterior/projection identity.

For each fixed finite Krylov depth r and mode k, the intended closure remains

```text
quantitative locality + physicality + commutation + weighted beta summability
  -> adjacent orbit-defect summability
  -> Cauchy / strong limits at fixed natural times
  -> nonzero time-zero excitation under those hypotheses
  -> one limiting discrete-time operator with compatible iterates
  -> H2 spacing-sensitive physical-time dynamics
  -> H3 OS Hamiltonian and H4 Wightman / energy-momentum mass gap.
```

The scalar fixed-rate bound `q0^floor(t/a_n) -> 0` for `t > 0`, `a_n -> 0`, explains why a spacing-independent finite-volume contraction cannot simply be relabeled a nontrivial physical-time semigroup. H2 needs actual scale-sensitive operator/generator data and a physical identification; escaping one no-go is not sufficient.

Detailed inputs and acceptance criteria: [ROADMAP](ROADMAP.md).

## 7. Verification scope and axiom dependencies

The latest theorem run built the #5212 implementation and CompileSmoke successfully: **9406 jobs**, including cached dependencies/scheduler jobs, not a fresh whole-repository build. The two changed files had **0 warnings / 0 errors**. Four regression examples cover the literal integral, two-step norm-loss telescoping, an L2 majorant, and a constant majorant.

The ten #5212 axiom-print outputs contain **no `sorryAx`**. Two declarations (`posteriorSchedule_append_singleton`, `posteriorStageResidualEnergy_nonneg`) use only `propext`, `Classical.choice`, and `Quot.sound`. The other eight also inherit five existing `native_decide`-generated dependencies from `periodicHypercubicIncidentPlaquettes_card_le_six` and `periodicHypercubicOtherAxis_card`. #5210--#5212 introduce none of these dependencies, but their L2 endpoints must not be described as standard-three-axioms-only. This is a statement about the checked endpoints, not a repository-wide axiom audit.

Diagnostic artifact: `11397893902`; SHA-256: `493a263900b9def8055af721ec19976018dab85028f15c1c78db5c9f828b2471`. Full names and verification rules are in the [ROADMAP](ROADMAP.md).

## 8. Restart and local checking

Read the latest source chain in sections 3--4, then the [bounded-continuous adjacent-tail receiver](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSweepStageBCFOscillationEnergyMajorantTail.lean). Keep the checked mathematical statements and their hypotheses separate from PR descriptions.

In an existing checkout with the pinned Lean toolchain available:

```bash
git fetch origin
git switch formal/real-hilbert-uniform-coercive-strong-limit
git pull --ff-only
lake exe cache get
lake build MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointStageResidualEnergyCompileSmoke
```

Do not run `lake update` merely to obtain current online APIs: preserve [lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json). For a new theorem PR, validate the exact head, actual Lean job, and matching receipt. For a README/ROADMAP-only change, verify the two-file diff; do not manufacture a new theorem-validation claim or trigger a redundant strict-Lean run.
