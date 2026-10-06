# MGAP4D Roadmap

**Status date: 2026-10-06 JST. Theorem snapshot: through merged [PR #5212](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5212).**

This roadmap separates actual finite-model results, proved implications whose hypotheses remain to be constructed, refuted routes, and future physical identifications. [README](README.md) is the overview; the Lean declarations linked below are the mathematical source of truth.

## 0. Authority checkpoint

| Item | Checkpoint |
| --- | --- |
| Unique theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing baseline | `c5e283ff596cfe00e2bb8ebf8fc92d1938b749a5` |
| Latest theorem-bearing PR | #5212, merged |
| Validated #5212 head | `014856b9cd02a56670beb891c1bb5b6895c26a4e` |
| Pinned Lean | `v4.30.0-rc2` |
| Pinned mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

The default branch `main` is not theorem authority. A docs-only commit can advance the branch without replacing the theorem-bearing baseline. This document records a fixed snapshot, not a prediction of the next branch HEAD.

Authority order remains: fresh exact theorem-carrier SHA; formal Lean artifacts at that SHA; README / ROADMAP; exact-head CI receipts; history. Preserve the pinned [toolchain](lean-toolchain), [manifest](lake-manifest.json), original measures, and original Hilbert carriers when continuing.

## 1. Retained foundations and recent milestones

### Finite-volume results and conditional continuum reductions

The retained finite-volume transfer lane has `kappa_12 >= 1/2304`, physical transfer-gap floor `>= 1/3072`, and `q0 = 3071/3072` under its existing theorem hypotheses. The completed physical pair non-top receiver supplies natural-time power decay. These bounds are not asserted for arbitrary coupling outside those hypotheses and are not a continuum physical mass.

H1-D4 identifies the independent-endpoint gauge-fixed pair sector with the physical pair carrier. The old completed H1-D5 compatibility is closed as a **positive-coupling SU(2) no-go**, not retained as an unproved input.

The SU(2) three-mode construction supplies finite orthonormal modes and a norm-one selected non-top excitation. The adjacent-Cauchy development theorem-generates fixed-natural-time limits and nonzero time-zero synthesis **once its finite Cauchy/summability inputs are supplied**. It does not by itself construct those inputs or a single physical-time continuum operator.

The orbit-wise telescoping estimate is

```text
||A^m x - B^m y||
  <= ||x-y|| + sum_(r<m) ||(A-B)(B^r y)||.
```

Thus fixed-depth, fixed-mode adjacent control is enough; whole-space operator-norm convergence is not required by this receiver. Same-volume normalized physical pair-transfer beta variation is explicitly bounded, leaving a weighted scalar beta-increment task rather than an unidentified coupling operator.

### Milestone map

| Milestone | Established result | Remaining boundary |
| --- | --- | --- |
| Through #5124 | Canonical finite reconstruction; two projective residuals combine into the squared coarse-physical projection defect V; growing-distance and adjacent-summability receivers | Quantitative model estimates and the physical identification still required |
| #5134 | Pair-Haar to genuine joint L2 half-density isometry using the actual positive density | Not an identification of physical transfer with conditional expectation |
| #5143--#5148 | Concrete link oscillation controls projection residuals; exact stage-profile and bounded-continuous dense-core majorant receivers | Construct the actual prefix-dependent witnesses and scalar tails; retain physicality separately |
| #5159--#5163 | Actual posterior one-link law, fixed-left Feller closure, and one-link variation propagation | Respect the observable, context, influence-data and regularity hypotheses |
| #5194--#5199 | Canonical posterior response bridge, uniform-Dobrushin infrastructure, and actual local-factor spatial covariance decay | Not yet the required arbitrary-observable six-spatial stage tail |
| #5200--#5206 | Full-sweep contraction and scalar scaling analysis; necessary finite-rate behavior | The proposed strict-interval certificate is subsequently refuted by #5207 |
| #5207 | Canonical closed strict-Dobrushin finite-positive-mass scaling certificate has no inhabitants | No conclusion about all other scaling routes or a critical point outside the interval |
| #5208 | Exact positive-scalar normalization and historical/continuous fiber identification on the stated a.e. contexts | No assertion on exceptional fixed fibers |
| #5209 | Genuine fiber and posterior laws agree under the actual joint measure, on a test-independent full-measure event | Joint-L2 operator identification is supplied by #5210 |
| #5210 | Literal posterior mean represents the existing joint CondExpL2 on the bounded strongly measurable core | Not an all-L2 literal integral formula |
| #5211 | Arbitrary finite chronological posterior schedules equal the existing projection sweep in L2 | Specified order retained; no cross-target commutativity |
| #5212 | Literal stage residual has exact projection-defect energy and Pythagorean norm loss; coefficient-one majorant receiver | The small residual majorant is still an explicit hypothesis |

The recent joint identities use arbitrary natural H, N > 0, beta >= 0. The adjacent three-mode route and H1-D5 counterexample are SU(2)-specific. General finite SU(N) identities do not automatically generalize the continuum SU(2) construction to all N.

## 2. Keep the objects and hypotheses separate

Use the following notation only as a guide to the existing definitions.

| Symbol | Existing object |
| --- | --- |
| `muJ` | Genuine ground-state joint probability law on `(L,R)` |
| `nuPost_(L,R,e)` | Actual posterior conditional law for the right target link e |
| `M_e` | Literal integral `F -> integral F(L,R[e <- g]) d nuPost_(L,R,e)` |
| `P_e` | Existing genuine joint `GroundStateSpatialLinkCondExpL2` |
| `S_pre` | Existing `realHilbertProjectionSweep` for an ordered finite link prefix |
| `V_(n,r,k)` | Adjacent common-marginal residual squared for the coarse embedded completed physical pair projection |

In particular `P_e` is not the physical transfer operator, and a right-link projection product is not automatically the coarse physical projection occurring in V.

For bounded strongly measurable F, #5211 proves

```text
[M_pre F]_(L2(muJ)) = S_pre [F]_(L2(muJ)).
```

For `G = M_pre F`, `x = [G]`, #5212 proves

```text
r_(pre,e) = G - M_e G,
r_(pre,e) in L2(muJ),

E_(pre,e)(F) := integral r_(pre,e)^2 d muJ
  = ||(I-P_e)x||^2
  = ||x||^2 - ||P_e x||^2.
```

The projection representative identities are a.e., not pointwise identities of arbitrary L2 representatives. Arbitrary-test Bochner change-of-variables and a.e.-congruence statements use the totalized integral; their lack of integrability premises must not be propagated into L2 claims without proof.

## 3. Immediate implementation order: construct the model majorant

### P1. Actual prefix-wise link variation to literal residual bounds — OPEN

Start from the existing [posterior variation propagation](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorVariationPropagation.lean), actual influence data, and [finite schedule identification](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointFiniteSchedule.lean).

For each required prefix pre and target e, construct a bound for the actual `G = M_pre F`, rather than introduce a new assumption that already states the final residual estimate. A useful intermediate form is

```text
|G(L,R) - G(L,R[e <- g])| <= delta_(pre,e)
```

for all inserted g on the appropriate contexts. Establish the fiber integrability needed to average this difference. For bounded-continuous initial observables, use fixed-left restrictions and the existing Feller results, or prove the corresponding regularity explicitly. Do not presume joint pointwise regularity merely from an a.e. L2 identity.

**Acceptance:** a theorem-generated pointwise or joint-a.e. bound on `|G - M_e G|`, with the actual propagated profile and all parameter/cutoff hypotheses shown. A context-dependent bound is acceptable if its L2 membership under muJ is also proved.

The existing [local-factor covariance decay](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalSpatialCovarianceDecay.lean) has an H- and N-independent prefactor on its canonical half-barrier interval, for distinct plaquette-remote ordered pairs. It permits `s >= 1`, with genuine exponential decay for `s > 1`. Uniform-Dobrushin results use their own smaller cutoff and `s > 8`. These are not interchangeable hypotheses, and a covariance bound for two local factors is not yet P1 for every required stage observable.

### P2. Stage energy and the exact six-spatial prefix interface — OPEN CONSTRUCTION; ENERGY RECEIVER CLOSED

Apply #5212 once P1 supplies either

```text
|r_(pre,e)| <= |b_(pre,e)| a.e.,  b_(pre,e) in L2(muJ),
```

or a nonnegative constant delta bound. The available outputs are

```text
E_(pre,e)(F) <= integral b_(pre,e)^2 d muJ,
E_(pre,e)(F) <= delta_(pre,e)^2.
```

No additional comparison coefficient is lost in this step. The majorant may still depend on volume or the observable unless P1 proves the required uniform control.

Next align the exact fixed-color enumeration and its prefix with the original stage vector, including the subtype-to-link map and the actual initial vector. Repetition is allowed in the general finite-schedule theorem, but the canonical fixed-color receiver has its own enumeration/freshness conditions. Neither reorder links nor infer commutation.

The existing [stage-profile receiver](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileOscillationMajorant.lean) yields the normalized form

```text
ProfileEnergy(f) <= (1/6) * sum_e delta(e)^2
```

when its concrete stage-oscillation witnesses are supplied. Either construct those witnesses with their required strong measurability and pointwise bounds, or prove the adapter from the exact per-stage residual bounds to the same local-profile quantities. An a.e. residual estimate is not silently substituted for a pointwise oscillation witness.

**Acceptance:** an actual per-link stage bound on the correct canonical prefix and a proved normalized profile-energy bound. Keep the existing factor `1/6`; introduce no untracked cardinality loss.

### P3. Bounded-continuous dense-core closure and support-distance tail — OPEN INPUTS; RECEIVER CLOSED

Use the [bounded-continuous closure](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileBoundedContinuousCoreClosure.lean) and [adjacent frozen-Krylov receiver](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSweepStageBCFOscillationEnergyMajorantTail.lean).

For every bounded-continuous joint observable O, construct stagewise nonnegative delta and dominate its normalized squared energy by one scalar function A_n on the actual joint L2 carrier:

```text
(1/6) * sum_e delta_(n,O)(e)^2 <= A_n([O]),
A_n is continuous in L2.
```

Then prove, at the actual frozen Krylov vector and for every fixed r,k,

```text
A_n(frozen_(n,r,k)) <= C_(r,k) * rho^D_(n,r,k) / (1-rho),
0 <= rho < 1,
n <= D_(n,r,k).
```

The pointwise oscillation profile need not itself be L2-continuous. Nor is a bounded-continuous representative of the frozen L2 vector required. Density extends an already proved continuous scalar inequality; it does not create a locality estimate from density alone.

**Acceptance:** the concrete fields required by `PhysicalYangMillsSU2AdjacentGroundStateSweepStageBCFOscillationEnergyMajorantPhysicalityTailInput`, including its own cutoff and loss-ratio conditions. The split physicality tail in that structure remains a separate task below.

## 4. Independent adjacent-scale obligations

### C1. Common-marginal physicality defect — OPEN

The total reconstruction variance is already

```text
V_(n,r,k) = ||Y_(n,r,k) - P_n^phys Y_(n,r,k)||^2.
```

The stage-profile route constructs a candidate in the common finite marginal, but the candidate's leakage from the coarse embedded completed physical pair carrier is separately measured. Prove the required tail for

```text
||Candidate_n(Y) - P_n^phys Candidate_n(Y)||^2.
```

Do not infer that this term vanishes because the candidate is a posterior average, a ground-state conditional expectation, or a vector in the same Hilbert space. A proof of fixed-space membership, projection equality, or the specified quantitative comparison is required. Check comparison direction: projection onto a larger subspace leaves a smaller residual.

Once locality and physicality inputs are available, the existing reconstruction receivers convert one total variance tail into bounds for both projective residuals. Taking a square root changes a rate rho to sqrt(rho); preserve that rate and its constants.

### C2. Physical transfer / reconstruction commutation — OPEN

For each fixed finite Krylov depth r and mode k, control the actual finite-vector mismatch schematically written as

```text
A_n(r,k) = ||T_n R_n^phys x_(n,r,k)
             - R_n^phys T_(n+1,beta_n) x_(n,r,k)||.
```

Use the existing normalized physical pair-transfer and canonical reconstruction definitions, not a posterior-sweep replacement. A summable bound is sufficient; a geometric bound is convenient. The receiver does not require whole-space operator-norm convergence or uniformity in unbounded Krylov depth.

**Acceptance:** the physical-commutation tail on the actual frozen orbit vectors, from Wilson/refinement data rather than a renamed H1-D5 compatibility assumption.

### C3. Explicit weighted beta trajectory — OPEN INPUT; COEFFICIENT CLOSED

The normalized same-volume transfer-response development supplies a majorant of the form

```text
b_n = C_norm(halfExtent(n+1), beta(n), beta(n+1))
        * |beta(n+1) - beta(n)|.
```

Prove summability, or an appropriate geometric upper bound, for a chosen trajectory. The normalization factors depend on volume and coupling; small unweighted beta increments alone are not enough. The trajectory must satisfy every cutoff used in the same construction.

**Acceptance:** a concrete trajectory theorem with the explicit weighted estimate. Satisfying this scalar condition alone does not solve H2 physical-time scaling, and the #5207 certificate cannot be inhabited by keeping a trajectory inside its refuted fixed strict interval.

## 5. H1-C3 closure and the subsequent physical layers

### H1-C3: fixed-natural-time existence — CONDITIONAL RECEIVERS CLOSED

For each fixed r,k, the intended actual-model chain is

```text
P1--P3: prefix locality -> stage profile -> frozen-vector tail
C1:     common-marginal physicality tail
  -> total reconstruction-variance tail
  -> geometric/summable projective residuals

C2: physical transfer/reconstruction commutation
C3: explicit weighted beta-increment control
  -> finite reconstruction/orbit-geometry summability
  -> adjacent orbit-mismatch summability
  -> fixed-natural-time Cauchy/strong limits
  -> norm-one nonzero time-zero excitation under those inputs.
```

The historical reductions through #5120/#5119/#5118/#5117, #5116/#5115/#5108, and #5106/#5098/#5096 remain reusable. The newer #5148 input is a more model-facing way of feeding the locality/physicality part of that chain. Preserve its inherited OS/projective-readout hypotheses as well as its quantitative fields.

### One limiting discrete-time transfer operator — STILL REQUIRED

Separate limits for each fixed natural m do not automatically define compatible iterates. Identify a common limiting domain/subspace, prove that the time-one action is well-defined, and establish

```text
T_infty^m z_(infty,0) = z_(infty,m).
```

Then transfer contraction and the stated non-top bounds on the justified domain.

### H2: spacing-sensitive physical time — STILL REQUIRED

For `a_n > 0`, `a_n -> 0`, a fixed `0 < q0 < 1` satisfies

```text
q0^floor(t/a_n) -> 0,  t > 0.
```

Applied on a sector with the corresponding uniform decay estimate, this is a collapse bound, not a construction of a nontrivial strongly continuous physical-time semigroup. Additional or replacement scale-sensitive operator/generator data and a physical time identification are necessary. A schematic rate such as `q_n = exp(-m_n a_n + o(a_n))` is not sufficient by itself to construct continuum dynamics.

Any new scaling route must respect the exact no-go results below. Do not infer a critical point or a valid continuum trajectory solely from the failure of the present route.

### H3/H4: OS Hamiltonian and Wightman mass gap — STILL REQUIRED

After actual continuum dynamics exist, identify the physical Hilbert space and generator, establish the relevant self-adjointness/positivity/vacuum properties and vacuum-orthogonal spectral lower bound, and verify the reconstruction and energy-momentum requirements for the intended Yang--Mills theory. Generic functional-analytic receivers or finite SU(2) test sectors are not a completed four-dimensional construction for the full gauge-group target.

## 6. Closed no-go routes

### N1. Old completed H1-D5 at positive SU(2) coupling

The old compatibility forces rank-one normalized transfer behavior, contradicted by the positive-coupling two-mode construction. Do not restore equivalent assumptions as vacuum/top alignment, exact completed cross-scale transfer compatibility, or an OS-boundary/physical-pair transfer identity by fiat. This is a specific route obstruction, not a nonexistence theorem for Yang--Mills theory.

### N2. Canonical strict-Dobrushin finite-positive-mass scaling: #5207

For fixed `s > 8`, the [generator-scaling structure](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFullSweepGeneratorScaling.lean) requires positive spacings tending to zero, couplings in `[0, beta_cut(s)]`, a finite positive mass m, and

```text
(1 - alphaBar(s,beta_n)) / a_n -> m.
```

The canonical full-sweep factor is `rho(s,beta) = exp(-(1-alphaBar(s,beta)))`. The necessary condition `alphaBar(s,beta_n) -> 1` conflicts with continuity and pointwise strictness on the compact closed interval: a convergent coupling subsequence would have a coefficient limit both equal to 1 and strictly below 1.

The [no-go file](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFiniteMassUniformDobrushinNoGo.lean) proves `impossible_inside_uniformDobrushinInterval` and `not_nonempty_inside_uniformDobrushinInterval` in the generator-scaling namespace.

**Status: refuted certificate, not an open construction task.** Earlier certificate-conditional scalar implications remain valid but have no inhabitant in this regime. The result neither supplies a critical coupling outside that interval nor rules out every different scaling design. Finite posterior locality estimates inside their valid interval remain useful independently of this no-go.

## 7. Source-level handoff

All listed files are under `MGAP4D/MathlibAnalytic/`.

| Read in this order | Purpose |
| --- | --- |
| [PosteriorJointStageResidualEnergy](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointStageResidualEnergy.lean) | #5212 exact energy, integrability, Pythagorean loss, a.e. majorant receiver |
| [PosteriorJointFiniteSchedule](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointFiniteSchedule.lean) | #5211 a.e. congruence and chronological projection-sweep identification |
| [PosteriorJointCondExpIdentification](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointCondExpIdentification.lean) | #5210 one-step canonical mean / posterior / genuine joint CondExpL2 |
| [FiberPosteriorJointAEBridge](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberPosteriorJointAEBridge.lean) | #5209 actual joint full-measure event |
| [FiberPosteriorMeasureBridge](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberPosteriorMeasureBridge.lean) | #5208 exact normalization and the historical representative boundary |
| [PosteriorVariationPropagation](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorVariationPropagation.lean) | Actual one-link variation estimate to iterate |
| [CanonicalSpatialCovarianceDecay](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalSpatialCovarianceDecay.lean) | #5199 local-factor spatial clustering with its exact cutoff/separation assumptions |
| [StageProfileOscillationMajorant](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileOscillationMajorant.lean) | Exact canonical prefix and normalized six-spatial profile interface |
| [BoundedContinuousCoreClosure](MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileBoundedContinuousCoreClosure.lean) | Continuous scalar majorant extension from the BCF dense core |
| [AdjacentBCFOscillationEnergyMajorantTail](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGroundStateSweepStageBCFOscillationEnergyMajorantTail.lean) | #5148 actual frozen SU(2) Krylov input, including separate physicality and loss-ratio fields |

Core #5212 endpoints in `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`:

```lean
posteriorSchedule_append_singleton
posteriorScheduleL2_append_singleton
projectionStageResidual_coeFn_eq_posteriorStageResidual
posteriorStageResidual_memLp_two
posteriorStageResidual_sq_integrable
posteriorStageResidualEnergy_eq_projectionResidualNormSq
posteriorStageResidualEnergy_eq_norm_loss
posteriorStageResidualEnergy_nonneg
posteriorStageResidualEnergy_le_of_ae_majorant
posteriorStageResidualEnergy_le_of_ae_bound
```

## 8. Proof dependencies and exact-head verification

### Endpoint-specific axiom scope

| Checked development | Standard-three-only endpoints | Endpoints also inheriting the five native-decide dependencies |
| --- | --- | --- |
| #5210: six printed endpoints | Two kernel/mean identities | Four CondExpL2 / MemLp / L2 / BCF endpoints |
| #5211: eight printed endpoints | Four a.e. congruence/schedule identities | Four L2/projection endpoints |
| #5212: ten printed endpoints | `posteriorSchedule_append_singleton`, `posteriorStageResidualEnergy_nonneg` | The other eight printed endpoints |

All these printed lists are free of `sorryAx`. The standard three are `propext`, `Classical.choice`, and `Quot.sound`. The additional existing dependencies are:

```text
periodicHypercubicIncidentPlaquettes_card_le_six._native.native_decide.ax_1_1
periodicHypercubicOtherAxis_card._native.native_decide.ax_1_1
periodicHypercubicOtherAxis_card._native.native_decide.ax_1_2
periodicHypercubicOtherAxis_card._native.native_decide.ax_1_3
periodicHypercubicOtherAxis_card._native.native_decide.ax_1_4
```

These PRs do not introduce the native-decide calls or new axiom declarations. They do inherit those dependencies. Do not claim that all endpoints use only the three standard axioms, and do not extrapolate the inspected lists to a repository-wide audit. Replacing the inherited finite-geometry native computations by kernel-checked proofs is a separate proof-hardening task, not a result of this documentation update.

### Latest theorem receipt: #5212

| Evidence | Value |
| --- | --- |
| Validated head | `014856b9cd02a56670beb891c1bb5b6895c26a4e` |
| [PR Lean Fast Check](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37434311434) | `37434311434`, completed / success |
| Actual Changed Lean job | `112172256508`, success |
| MCP receipt publisher | `112173652910`, success |
| Exact-head status | `chatgpt-ci-receipt/PR Lean Fast Check`, success for the same run |
| Diagnostic artifact | `11397893902` |
| Artifact SHA-256 | `493a263900b9def8055af721ec19976018dab85028f15c1c78db5c9f828b2471` |
| Final implementation blob | `130f4df7e69fef35a8b4d6b62586253680cdce29` |
| Build result | 9406 jobs, including cached dependencies/scheduler jobs |
| Changed-file warnings / errors | 0 / 0 |
| Regression coverage | Four examples, seven export checks, ten axiom-print commands |

The examples include the fully written literal residual integral, two-stage norm-loss telescoping even for repeated targets, an L2 majorant, and a constant majorant. The sum of noncommuting stage energies is not identified with the squared total vector defect.

The first complete #5212 implementation compiled but had one unused-binder warning. The final head removes that binder without changing a theorem statement, assumption, test, or linter setting. The receipt above belongs to the theorem PR, **not to a later docs-only commit**.

## 9. Lean and CI lessons to preserve

Use pinned declarations rather than guessed names or current online signatures. In particular:

- Local notation is not a namespace: use `Measure.prod muH ...` rather than relying on a notation token followed by `.prod`. Keep notation names distinct from named arguments, as in `(Gauge := GaugeT)`.
- Use the pinned `MemLp.ae_eq hfg hf` with the correct equality orientation; do not assume `MemLp.congr` exists.
- When reversing an inferred `Eventually.mono` result, prefer pointwise reversal inside `.mono`, or an explicitly typed `EventuallyEq.symm`. Uncontrolled field resolution can unfold a.e. to its null-set equation and select the wrong `Eq.symm`.
- Use `change`, local equalities, and `calc` to control bundled maps, subtype coercions, and exact measure carriers. Do not unfold definitions that have already reduced.
- Preserve Fubini's direction and measurability requirements. The reverse of an iterated-a.e. implication is not automatic. Keep test-independent kernel events distinct from a.e. representative events for a given observable.
- The static declaration-header checker can misread a declaration-like line inside a block comment. Rephrase the documentation rather than disable the guard. Remove new-file warnings without weakening tests or linting.

For theorem-bearing PRs, require an unchanged exact head, the actual Lean build job's success, and a matching exact-head receipt. Inspect changed sources and diagnostics, not merely the receipt publisher's status. Cached scheduler counts are not counts of freshly compiled repository modules.

For README/ROADMAP-only PRs, verify that the diff contains only those files. The existing path-filtered Lean workflow does not require a redundant strict-Lean run; absence of a run is not a new theorem GREEN. Do not modify workflows or manufacture a code change to trigger CI for prose.

## 10. Restart target

Re-observe the theorem-carrier branch first. At this snapshot the latest theorem-bearing merge is `c5e283ff596cfe00e2bb8ebf8fc92d1938b749a5` (#5212), even if a subsequent docs-only merge has advanced HEAD.

**Next deliverable:** construct the actual prefix-specific posterior residual majorant from the link-variation machinery, prove its required regularity and parameter uniformity, and connect it to the exact canonical stage-profile interface. The normalization, joint-a.e., one-step L2, finite-schedule, and stage-energy identifications are already available; do not restart them or replace the missing majorant by another receiver that assumes it.

Keep common-marginal physicality, physical reconstruction commutation, weighted beta summability, limiting-operator compatibility, and physical-time scaling visible as distinct remaining obligations.
