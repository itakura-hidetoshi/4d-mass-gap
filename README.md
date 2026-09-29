# MGAP4D

Lean/mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Current result:** the exact cyclic target-residual forcing telescope is now connected to the genuine terminal second-sweep profile. The next step is a volume-uniform, beta-small analytic estimate for that forcing, not another reconstruction of the cyclic list or its L2 carrier.

## Authority checkpoint — 2026-09-29 JST

| Item | Authoritative value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing baseline | `4b11fd20cd2bbcba5a84bec2fedafc2aaaa4e47c` — merged PR #4921 |
| Validated #4921 PR head | `827068e4ee47cd6ad35c2f208506ea82f817d493` |
| Exact-head validation | [PR Lean Fast Check, run 36528060981](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36528060981): completed / success; matching completion receipt: success |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

[Open the authoritative branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Proof roadmap](ROADMAP.md) · [Formal analytic modules](MGAP4D/MathlibAnalytic)

The GitHub default branch `main` is **not** theorem authority. Documentation-only commits may follow the theorem-bearing baseline above; they do not advance the mathematical result or create a new Lean validation receipt.

Authority order: fresh exact theorem-carrier SHA; formal Lean artifacts at that SHA; README / ROADMAP; exact-head CI evidence; history or conversation memory. The run above validates the stated PR head, not an untested later commit.

## What is proved, and what remains open

The repository contains a developed finite-volume Wilson / Osterwalder--Schrader / physical-transfer construction, an **exact beta-zero physical transfer gap of 1**, and the positive-beta response / RMS / bidirectional Schur machinery used below.

It does **not** yet contain a complete continuum four-dimensional Yang--Mills existence and mass-gap proof. The active bottleneck remains the finite-volume positive-beta physical gap: quantitatively compare a noncommutative same-color one-link sweep with the genuine color-block projection, uniformly in volume.

| Layer at the current frontier | Status |
| --- | --- |
| Exact renewal, cyclic second visit, off-diagonal source set | Proved |
| Bounded representatives for every cyclic prefix and source step | Proved |
| Actual source residual = trajectory residual; suffix/pre profile classification | Proved |
| Signed target-cross-residual telescope and commutator decomposition | Proved |
| Commutator coefficient vanishes at beta zero | Proved |
| Nonexpansive target-residual feedback | Proved |
| Ordered forcing-budget telescope and cyclic terminal-profile receiver | Proved |
| Beta-small terminal Schur receiver | Proved implication; its semantic premise is still required |
| Forcing-to-influence/profile analytic comparison | Open |
| Strict quantitative next-defect contraction | Open |
| `delta(beta) < 1/6` and positive-beta physical transfer gap | Open |
| Thermodynamic limit and continuum OS / Wightman mass-gap construction | Open downstream goals |

## 1. Exact sweep/block geometry

For spatial color `c`, write `B_c` for the genuine color-block conditional expectation, `S_c` for one complete canonical same-color one-link sweep, and `L_c(f)` for its path loss. Define

```text
D_c(f) = ||S_c f - B_c f||^2.
```

At beta zero, `S_c = B_c` exactly. At positive beta, equal common fixed spaces do not imply commutativity or equality of these operators. The defect measures the failure of one pass to land in the block-fixed space.

PRs #4892--#4896 give the exact renewals

```text
D_c(f) = L_c(S_c f) + D_c(S_c f)
Dmean(f) = Lterm(f) + Dnext(f),
```

where the latter quantities are six-color averages. The link-indexed terminal profile is normalized by

```text
(1/6) * sum_e terminalProfile(e)^2 = Lterm(f).
```

For a canonical target split

```text
canonicalList = pre ++ target :: suffix,
```

the first post-target vector and the exact between-visits order are

```text
x0 = P_target (sweep pre f)
sources = suffix ++ pre.
```

The source list contains exactly every other same-color link, without reordering: `(suffix ++ pre).toFinset = Finset.univ.erase target`.

## 2. Actual cyclic source updates are connected to the analytic carrier

PR #4901 connects cyclic membership to the existing exact `fullDifferenceL2 = directDifferenceL2 + responseL2` and negative transposed law-response identities. PRs #4904--#4907 and #4909 supply the quantitative estimates and bounded representatives for each actual transition

```text
x_after = P_source x_before
sourceResidual = x_before - x_after.
```

The centered backward direct-variance and law-response estimates retain their existing Harnack and transposed pin-free coefficients. These are separate estimates; their existence is not yet the required small bound for the total target forcing.

PR #4911 proves the exact profile classification:

```text
source in suffix:  cyclicStageResidualEnergy = originalProfile(source)^2
source in pre:     cyclicStageResidualEnergy = terminalProfile(source)^2.
```

This reuses the unique-stage API from #4856. PR #4910 was closed **without merge** as redundant; it is not a theorem-bearing milestone.

Sources: [stage-residual quantitative bridge][stage-quantitative], [suffix/pre classification][profile-classification].

## 3. Signed telescope, commutator forcing, nonexpansive feedback

Write

```text
r_t(x) = x - P_t x
cross(t,s,x) = (I - P_t) ((I - P_s) x)
C(t,s) = P_t P_s - P_s P_t.
```

PRs #4912--#4915 prove the exact identities

```text
r_t(P_s x) = r_t(x) - cross(t,s,x)
cross(t,s,x) = C(t,s)(P_t x) + cross(t,s,r_t(x)),
```

with target idempotence for the commutator identity. Starting at target-fixed `x0`, the terminal target residual is the negative signed sum of the successive cross residuals along the actual trajectory. PR #4913 identifies the terminal profile with the norm of that signed sum.

PRs #4916--#4918 define and bound the forcing coefficient

```text
c_comm(t,s;beta) = ||C(t,s)||
c_comm(t,s;0) = 0.
```

For the self-adjoint idempotent physical projections, PR #4919 gives

```text
r_t(P_s x) = -C(t,s)(P_t x) + r_t(P_s(r_t(x)))
||r_t(P_s(r_t(x)))|| <= ||r_t(x)||,
```

and hence

```text
||r_t(P_s x)|| <= c_comm(t,s;beta) * ||P_t x|| + ||r_t(x)||.
```

The feedback is nonexpansive: it introduces no extra per-step multiplier. The projected-input factor `||P_t x||` is retained rather than weakened to `||x||` in the current terminal-budget theorem.

Sources: [signed telescope][signed-telescope], [commutator coefficient][commutator-coefficient], [nonexpansive step][nonexpansive-step].

## 4. Current theorem: terminal profile is bounded by the cyclic forcing budget

PR #4920 defines the ordered accumulated forcing recursively:

```text
Budget([], x) = 0
Budget(source :: rest, x)
  = forcing(source,x) + Budget(rest, P_source x).
```

Given a one-step bound for every source and vector,

```text
||r_t(P_source x)|| <= forcing(source,x) + ||r_t(x)||,
```

it proves

```text
||r_t(sweep sources x)|| <= Budget(sources,x) + ||r_t(x)||.
```

PR #4921 specializes this to the genuine cyclic terminal carrier. Since `P_target x0 = x0`, the initial residual disappears:

```text
terminalProfile(target) <= Budget(suffix ++ pre, x0).
```

Its commutator specialization uses exactly

```text
forcing(source,x) = c_comm(target,source;beta) * ||P_target x||.
```

Every contribution is evaluated immediately before its actual source update. There is no source reordering, arbitrary factor two, or finite-cardinality Cauchy loss.

The general receiver's `hStep` is universally quantified over the stated L2 carrier. An estimate established only for selected bounded trajectory states must be extended to that hypothesis, or used through a separately proved restricted-trajectory receiver; that distinction is not implicit.

Sources: [generic forcing telescope][forcing-telescope], [cyclic terminal-profile receiver][cyclic-forcing].

## 5. Beta-small Schur receiver already available

PR #4902 preserves the small external forcing rather than replacing it by the original profile with coefficient one. With the existing physical transpose action

```text
(K^T v)(i) = sum_j K(j,i) * v(j),
```

the premise

```text
terminal <= K^T original + K^T terminal
```

implies, on the certified physical cutoff,

```text
(1 - q_phys(s,beta))^2 * Lterm(f)
  <= q_phys(s,beta)^2 * L(f).
```

The endpoint identity `q_phys(s,0) = 0` is also proved. This is a proved conditional receiver, not a proof that the actual cyclic forcing satisfies its premise. Keep it distinct from the older coefficient-one receiver in #4898.

Source: [beta-small terminal Schur feedback][beta-small-schur].

## 6. Next mathematical work

**Immediate target:** derive a volume-uniform, beta-small forcing-to-influence/profile comparison on the actual cyclic carrier. Reuse the exact direct/backward/law-response decomposition, the stage-residual estimates, and the suffix/pre classification. Preserve both the projected-input factor and the established source/target orientations until the relevant comparison is proved.

`c_comm(t,s;0) = 0` alone does not prove a uniform positive-beta estimate. Likewise, a bound for the operator coefficient alone does not automatically turn `c_comm * ||P_t x||` into a local source-residual cost or a Schur summable profile.

The intended remaining route is

```text
beta-small analytic forcing comparison
  -> actual terminal <= K^T original + K^T terminal
  -> existing #4902 beta-small Schur receiver
  + strict next-defect contraction (or equivalent positive renewal bound)
  -> Dmean(f) <= delta(beta) * ||f||^2
  -> certify 0 <= delta(beta) < 1/6
  -> existing physical transfer-gap receiver.
```

The strict renewal input `Dnext <= rhoDefect * Dmean`, with `rhoDefect < 1`, remains a separate open quantitative requirement. Do not divide by `1-q_phys` or `1-rhoDefect` before proving positivity.

The existing defect-margin receiver yields

```text
(3/8) * (1/6 - delta(beta)) <= physical transfer gap.
```

This perturbative lower bound is distinct from the exact beta-zero result `gap_0 = 1`. The thermodynamic and continuum constructions remain downstream of a volume-uniform finite-volume gap.

## Lean / CI workflow

Freshly observe the authoritative branch and exact PR head before changing or classifying a theorem. A theorem-bearing GREEN requires the completed exact-head `PR Lean Fast Check` and its matching success receipt; the receipt alone is not the mathematical validation.

PRs #4903 and #4908 improved cache reuse. The current workflow separates pinned `.lake/packages` dependencies from the evolving `.lake/build` project artifacts and retains dependency-aware `lake build`. The duplicate direct Lean elaboration pass is disabled in GitHub PR CI, not the authoritative build.

README / ROADMAP-only changes are excluded by the Fast Check path filters. Do not dispatch Strict Lean, warm caches, or manufacture a theorem receipt for a docs-only update.

On a Lean failure, inspect the entire changed module, CompileSmoke, imports, dependent signatures, local instances, and pinned mathlib APIs. Prefer explicit `calc`, `congrArg`, and focused `simpa only`; preserve coefficient orientation, avoid arbitrary L2 pointwise representatives, and do not assume positive-beta commutativity. Detailed restart instructions and the milestone ledger are in [ROADMAP.md](ROADMAP.md).

[stage-quantitative]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceStepQuantitative.lean
[profile-classification]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceStepProfileClassification.lean
[signed-telescope]: MGAP4D/MathlibAnalytic/RealHilbertProjectionSweepTargetCrossResidualTelescoping.lean
[commutator-coefficient]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetSourceCommutatorCoefficient.lean
[nonexpansive-step]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetResidualCommutatorNonexpansiveStep.lean
[forcing-telescope]: MGAP4D/MathlibAnalytic/RealHilbertProjectionSweepTargetResidualForcingBudgetTelescope.lean
[cyclic-forcing]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTerminalProfileForcingBudget.lean
[beta-small-schur]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointTerminalProfileBetaSmallSchurFeedback.lean
