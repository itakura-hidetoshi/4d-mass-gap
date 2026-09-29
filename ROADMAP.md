# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-29 JST

| Item | Value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Authoritative theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing baseline | `4b11fd20cd2bbcba5a84bec2fedafc2aaaa4e47c` |
| Latest theorem merge | [PR #4921](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4921) |
| Validated #4921 head | `827068e4ee47cd6ad35c2f208506ea82f817d493` |
| Exact-head CI | [PR Lean Fast Check 36528060981](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36528060981), completed / success; matching receipt: success |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

The default branch `main` is not theorem authority. A later README / ROADMAP-only commit is a documentation checkpoint, not a new theorem baseline or a new Lean receipt. Re-observe the live branch before continuing; the table records this document's theorem checkpoint rather than predicting the moving branch HEAD.

Authority order is: fresh exact theorem-carrier SHA; formal Lean artifacts; README / ROADMAP; exact-head CI evidence; history / memory.

## 0. Current boundary and immediate objective

The finite-volume Wilson / OS / physical-transfer construction, the exact beta-zero physical gap, and the established response / RMS / Schur infrastructure are available. The positive-beta finite-volume physical gap is not yet closed, and neither is the continuum Yang--Mills existence and mass-gap theorem.

**The immediate objective after #4921 is the beta-small analytic forcing comparison.** The following are no longer the missing steps: cyclic list geometry, bounded representatives for intermediate cyclic states, exact stage-residual identification, suffix/pre classification, signed cross-residual telescoping, nonexpansive feedback, and the terminal forcing-budget receiver.

There are two distinct quantitative tasks still to close:

1. obtain the actual beta-small terminal-profile recurrence from the cyclic source-update / commutator forcing;
2. prove strict next-defect contraction, or an equivalent positive renewal lower bound.

The beta-small Schur implication needed after the first task is already proved in #4902. Do not rebuild it or weaken away its `q_phys^2` factor.

## 1. Fixed notation and the gap receiver

For spatial color `c`:

```text
B_c       = genuine color-block conditional expectation
S_c       = one complete canonical same-color one-link sweep
L_c(f)    = exact one-pass path loss
D_c(f)    = ||S_c f - B_c f||^2

L(f)      = (1/6) * sum_c L_c(f)
Dmean(f)  = (1/6) * sum_c D_c(f)
Lterm(f)  = (1/6) * sum_c L_c(S_c f)
Dnext(f)  = (1/6) * sum_c D_c(S_c f).
```

The obstruction identities retained from the existing construction are

```text
E_6sp(f) = L(f) + Dmean(f)
FullSweepMean(f) = MeanProjectedNormSq(f) + Dmean(f).
```

The existing physical-sector defect-margin receiver accepts

```text
Dmean(f) <= delta * ||f||^2
0 <= delta < 1/6
```

and yields

```text
(3/8) * (1/6 - delta) <= physical transfer gap.
```

The target is an explicit volume-independent positive-beta interval and a certified `delta(beta) < 1/6`, not merely a finite-dimensional constant depending on the lattice size.

## 2. Retained exact geometry — #4887--#4899

### 2.1 Beta zero and positive-beta common fixed spaces

The pair-Haar commutation and complete-sweep identities in #4887--#4888 are transported to the genuine beta-zero carrier in #4889:

```text
S_c,0 = B_c,0
D_c,0(f) = 0
Dmean_0(f) = 0.
```

The exact beta-zero physical transfer gap remains `gap_0 = 1`. Substituting `delta(0)=0` in the later perturbative receiver gives a weaker bound, not a replacement for that exact theorem.

For all `beta >= 0`, #4890 identifies the common fixed geometry:

```text
(forall e in color c, P_e x = x) <-> B_c x = x
S_c x = x <-> B_c x = x.
```

This does not imply positive-beta pairwise commutativity or `S_c = B_c`. PR #4891 identifies the defect with the terminal color residual:

```text
S_c f - B_c f = S_c f - B_c(S_c f).
```

Thus zero defect is exactly the condition that one pass lands in the block-fixed space, equivalently that the next pass fixes that output.

### 2.2 Renewal and terminal profile

PRs #4892--#4893 give the energy and vector renewals:

```text
D_c(f) = L_c(S_c f) + D_c(S_c f)
defectVector_c(f)
  = residualVectorSum_c(S_c f) + defectVector_c(S_c f).
```

PR #4896 introduces the terminal profile and six-color normalization:

```text
terminalProfile_c(e) = originalProfile_c(S_c f, e)
sum_{e in c} terminalProfile_c(e)^2 = L_c(S_c f)
(1/6) * sum_e terminalProfile(e)^2 = Lterm(f)
Dmean(f) = Lterm(f) + Dnext(f).
```

PR #4897 supplies the terminal response-energy bound on its certified response cutoff:

```text
terminalResponseEnergy <= rhoResp(s,beta) * ofReal(6 * Lterm(f)),
```

using the existing strict volume-independent response coefficient. The response coefficient and the physical Schur coefficient have their own certified hypotheses; neither should be silently substituted for the other.

### 2.3 Cyclic carrier and source set

Fix

```text
canonicalList = pre ++ target :: suffix
x0 = P_target (sweep pre f)
cyclicSources = suffix ++ pre.
```

PR #4894 identifies the second target visit with the target residual after exactly this cyclic trajectory. PR #4895 supplies the bounded concrete terminal representative. PR #4899 proves

```text
source in suffix ++ pre <-> source != target
(suffix ++ pre).toFinset = Finset.univ.erase target
```

inside the fixed-color fiber, including the off-diagonal conclusion after forgetting the subtype. The list order is not replaced by an arbitrary enumeration.

## 3. Actual source-update semantics and exact step carrier — #4901, #4904--#4909

PR #4901 discharges the off-diagonal premises in the existing source-update identities for each cyclic source:

```text
fullDifferenceL2 = directDifferenceL2 + responseL2
backwardLawResponse = -transposedCanonicalResponse.
```

These identities concern the explicit bounded representative and its stated measures, not pointwise values of an arbitrary L2 equivalence class.

PR #4905 extends bounded representatives from the terminal cyclic state to every prefix `(suffix ++ pre).take k`. PR #4906 supplies bounded representatives before and after one actual update. PR #4907 proves the coefficient-one vector and energy identifications

```text
x_after = P_source x_before
sourceResidual = x_before - x_after
||sourceResidual||^2 = ||x_before - x_after||^2.
```

PR #4904 specializes the existing direct/backward quantitative estimates to cyclic sources; #4909 charges those estimates directly to the exact trajectory energy

```text
E_step = ||x_before - x_after||^2.
```

For clarity, set `H_beta = (exp(32 * beta))^2` and let `b(s,beta)` denote the existing canonical half-barrier pin-free coefficient. The source-step theorem retains the ENNReal bounds

```text
backwardDirectVarianceEnergy
  <= ofReal(H_beta) * ofReal(E_step)

backwardLawResponseEnergy
  <= ofReal(K_pin(source,target)^2)
     * (1 - ofReal(b(s,beta)^2))^(-1)
     * ((ofReal(H_beta) + 1) * ofReal(E_step)).
```

These abbreviate the exact vacuum / heat-bath integrals in the theorem; they do not identify differently indexed measures or replace ENNReal inverses by real division. The response estimate requires the certified physical cutoff. The direct and response branches remain separate; summing or squaring them is not a free step.

The transposed coefficient is `K_pin(source,target)`. Do not infer symmetry or identify it with a different physical envelope without the relevant comparison theorem.

Primary modules: [source-update semantics][source-semantics], [source-update quantitative estimates][source-quantitative], [cyclic prefix representatives][prefix-representatives], [step carrier][step-carrier], [step residual][step-residual], [stage-residual quantitative bridge][stage-quantitative].

## 4. Exact forcing/feedback profile classification — #4911

The cyclic source residual has two exact interpretations:

```text
suffix = before ++ source :: after:
  E_step = originalProfile(source)^2

pre = before ++ source :: after:
  E_step at cyclic prefix (suffix ++ before)
    = terminalProfile(source)^2.
```

This is the required classification of first-sweep forcing versus second-sweep feedback at the source-residual level. It uses the existing #4856 unique-stage local-profile theorem and proves freshness from canonical-list nodup.

PR #4910 was closed **unmerged**, because it duplicated that #4856 surface. Reuse the existing theorem; do not reopen the redundant PR.

Source: [cyclic source-step profile classification][profile-classification].

## 5. Signed target-cross-residual telescope — #4912--#4913

For continuous linear maps on the stated real normed space, define

```text
r_t(x) = x - P_t x
cross(t,s,x) = (x - P_s x) - P_t(x - P_s x).
```

PR #4912 proves the purely linear identity

```text
r_t(P_s x) = r_t(x) - cross(t,s,x).
```

Iterating in the actual order, with `x_(k+1) = P_(s_k) x_k`, gives

```text
r_t(x_m) = r_t(x0) - sum_k cross(t,s_k,x_k).
```

For target-fixed `x0`, the initial residual vanishes. PR #4913 specializes this to the genuine cyclic second visit and proves

```text
terminalProfile(target) = ||sum_k cross(target,s_k,x_k)||.
```

The vector sum also splits exactly into suffix and pre contributions. Signs are retained until the stated norm identity; no triangle or cardinality estimate is built into the signed telescope.

Sources: [generic signed telescope][signed-telescope], [physical cyclic telescope][cyclic-telescope].

## 6. Commutator forcing and its beta-zero anchor — #4914--#4918

PR #4914 packages `cross(t,s)` as the continuous linear map `(I-P_t) comp (I-P_s)` and splits its input into projected and residual parts. With

```text
C(t,s) = P_t P_s - P_s P_t,
```

and target idempotence, #4915 proves

```text
cross(t,s,P_t x) = C(t,s)(P_t x)
cross(t,s,x) = C(t,s)(P_t x) + cross(t,s,r_t(x)).
```

PR #4916 transports the beta-zero pair-Haar commutation theorem to the genuine joint L2 carrier, including the injective measure-equality cast, and proves exact vanishing of the physical commutator and projected forcing at beta zero.

PR #4917 defines

```text
c_comm(t,s;beta) = ||C(t,s)|| >= 0
c_comm(t,s;0) = 0
||C(t,s)(P_t x)|| <= c_comm(t,s;beta) * ||P_t x||.
```

PR #4918 combines this with the forcing/feedback split. Its physical full-norm bound is also available through projection contraction, but the later cyclic budget retains the sharper projected-input factor.

**Boundary:** exact endpoint vanishing is not a proved uniform-in-volume modulus at positive beta. Moreover, control of `c_comm` alone does not identify its projected-input norm with the source-residual energy in section 4. That analytic comparison remains to be established.

Sources: [linear split][linear-split], [commutator forcing][commutator-forcing], [beta-zero commutator][zero-commutator], [coefficient][commutator-coefficient], [cross-residual receiver][cross-receiver].

## 7. Nonexpansive target-residual update — #4919

For self-adjoint idempotent projections, the exact update is

```text
r_t(P_s x) = -C(t,s)(P_t x) + r_t(P_s(r_t(x))).
```

Both the source projection and the target residual projection are nonexpansive, so

```text
||r_t(P_s(r_t(x)))|| <= ||r_t(x)||
||r_t(P_s x)|| <= c_comm(t,s;beta) * ||P_t x|| + ||r_t(x)||.
```

This is the correct additive list-induction form. At beta zero the forcing coefficient is zero. Nonexpansiveness here is not the strict next-defect contraction required later; these are different statements.

Source: [nonexpansive target-residual step][nonexpansive-step].

## 8. Ordered forcing telescope and terminal receiver — #4920--#4921

The generic accumulated budget is

```text
Budget([],x) = 0
Budget(source :: rest,x)
  = forcing(source,x) + Budget(rest,P_source x).
```

PR #4920 proves, from a supplied one-step hypothesis,

```text
||r_t(sweep sources x)|| <= Budget(sources,x) + ||r_t(x)||.
```

For `P_t x = x`, only the budget remains. PR #4921 connects this to the exact physical terminal-profile norm:

```text
terminalProfile(target) <= Budget(suffix ++ pre, x0).
```

The commutator specialization has no supplied perturbative hypothesis; it instantiates the already-proved #4919 estimate with

```text
forcing(source,x) = c_comm(target,source;beta) * ||P_target x||.
```

This is an unconditional structural bound at each allowed physical beta, **not** a beta-small Schur bound for its right-hand side.

### Quantifier boundary for the next analytic theorem

The general #4921 receiver assumes `hStep` for **every source and every vector in the stated joint L2 space**. The bounded-concrete step machinery instead gives estimates on its explicit representatives and trajectories.

To connect them, either prove the needed universally quantified one-step inequality, or prove a trajectory-restricted telescope with the appropriate invariant-domain hypotheses and then specialize it. A bounded-core or off-diagonal estimate cannot be silently passed as the current universal `hStep`.

Alternatively, retain the commutator-budget conclusion and compare that budget directly to the desired profile. If taking the operator norm loses essential cancellation, use an analytically justified forcing in the general route rather than assert an unsupported termwise domination of `c_comm * ||P_t x||` by a source residual.

Sources: [generic forcing telescope][forcing-telescope], [cyclic terminal receiver][cyclic-forcing].

## 9. Beta-small Schur receiver — already proved in #4902

Let `O` and `T` be the original and terminal link profiles. Fix the actual physical envelope and its transpose convention:

```text
(K^T v)(i) = sum_j K(j,i) * v(j).
```

Under `s > 1`, `beta >= 0`, the certified physical cutoff, and the semantic premise

```text
T <= K^T O + K^T T,
```

#4902 applies the existing transpose Schur estimate twice and proves

```text
(1-q_phys(s,beta))^2 * Lterm <= q_phys(s,beta)^2 * L.
```

It also proves `q_phys(s,0) = 0`. The exact six-color normalization is preserved and no division is used. The older #4898 receiver assumes `T <= O + K^T T` and only yields `(1-q_phys)^2 * Lterm <= L`; do not discard the sharper forcing structure by choosing that coarser form unnecessarily.

The semantic premise for the actual cyclic terminal profile is still OPEN. Sections 3--8 provide its carrier and algebra, not yet the beta-small analytic estimate that supplies it.

Source: [beta-small terminal-profile Schur feedback][beta-small-schur].

## 10. Next theorem units and completion criteria

### F1. Beta-small analytic comparison — OPEN, immediate task

Work on the actual ordered cyclic trajectory, using the existing off-diagonal source set and bounded representatives. Combine the exact physical full/direct/response identity, backward variance / mean split, current-value reanchoring, and negative transposed response identity with the genuine target forcing.

The output must be a proved one-step or accumulated-budget estimate that can be charged to the actual source profiles with explicit, volume-independent beta-small coefficients. Preserve the actual kernel orientation and carrier measures. Discharge the quantifier/domain distinction in section 8.

A comparison for an abstract commutator coefficient may be useful, but is not by itself completion of F1. In particular, do not infer

```text
c_comm * ||P_t x|| <= smallKernel * ||x - P_s x||
```

without proving it on the required domain. Keep the projected factor and any cancellation visible until the chosen estimate is justified.

### F2. Assemble the actual terminal recurrence — OPEN

Use the exact suffix/pre source-energy classification from #4911, the signed or nonexpansive telescope, and the F1 estimate to obtain the actual profile inequality required by #4902:

```text
T <= K^T O + K^T T.
```

The kernel must be the receiver's certified physical envelope, or be related to it by a proved domination theorem with the right index orientation. If a different envelope is necessary, certify its own row/column bounds instead of reusing an unrelated `q_phys`.

Then apply #4902 directly. After certifying `1-q_phys > 0`, the desired usable upper bound has the shape

```text
Lterm <= eta(beta) * L,
```

with the small factor retained. Do not impose a numerical positive-beta interval before the coefficients are closed.

### F3. Strict renewal contraction — OPEN, separate input

Prove

```text
Dnext <= rhoDefect(beta) * Dmean
rhoDefect(beta) < 1,
```

or an equivalent uniform estimate `kappa(beta) * Dmean <= Lterm` with `kappa(beta) > 0`.

Use the exact renewal `Dmean = Lterm + Dnext`. Mere monotonicity `Dnext <= Dmean`, nonexpansive source feedback, and qualitative cyclic-projection convergence do not provide the required strict volume-uniform constant.

### F4. Defect margin and positive-beta finite-volume gap — OPEN

Once the actual beta-small Schur premise and strict renewal estimate are proved, the coefficient-preserving assembly has the target form

```text
(1-q_phys)^2 * ((1-rhoDefect) * Dmean) <= q_phys^2 * L.
```

This is the planned combination of the existing receivers after their missing hypotheses are supplied, not an assertion that those hypotheses are already closed.

Prove all positivity conditions before division. Use the existing physical-sector energy control to derive

```text
Dmean(f) <= delta(beta) * ||f||^2
0 <= delta(beta) < 1/6.
```

Then invoke the existing transfer-gap receiver. Extend any bounded-core estimate to the full genuine joint L2 carrier through the established density / continuity machinery. Record the full volume-independent interval, coefficient, and physical-sector assumptions.

### F5. Thermodynamic and continuum construction — downstream OPEN

After the volume-uniform finite-volume gap, advance compatible finite-volume restrictions/embeddings, vacuum control, the thermodynamic limiting state, and transfer/semigroup compatibility. Prove persistence of the gap on the correct limiting carrier.

The later continuum work includes the Euclidean field limit, continuum OS axioms, reflection-positive reconstruction, strongly continuous time translations, a self-adjoint Hamiltonian, vacuum/sector identification, and the transfer-gap-to-Hamiltonian-gap bridge leading to Wightman reconstruction.

A finite-volume gap alone is not the continuum theorem. These remain constructive downstream tasks, not consequences claimed by the present receivers.

## 11. Milestone ledger after the previous #4899 checkpoint

The theorem entries below are included in the exact baseline. A stacked PR may have been merged through its parent branch rather than directly into the theorem-carrier.

| PR | Classification | Contribution |
| --- | --- | --- |
| #4900 | Merged, docs only | Previous README / ROADMAP checkpoint at #4899 |
| #4901 | Merged theorem | Actual cyclic source-update semantic identities |
| #4902 | Merged theorem | Beta-small transpose Schur receiver; `q_phys(s,0)=0` |
| #4903 | Merged CI infrastructure | Canonical-base cache reuse |
| #4904 | Merged theorem | Quantitative cyclic direct/backward/law-response estimates |
| #4905 | Merged theorem | Bounded representatives for every cyclic prefix |
| #4906 | Merged theorem | Exact bounded before/after source-step carrier |
| #4907 | Merged theorem | Source residual = actual stage residual, vector and energy |
| #4908 | Merged CI infrastructure | Split dependency/project caches; remove duplicate direct elaboration |
| #4909 | Merged theorem | Quantitative costs charged to exact stage-residual energy |
| #4910 | Closed, NOT merged | Redundant unique-stage theorem; reuse #4856 |
| #4911 | Merged theorem | Exact original/terminal profile classification |
| #4912 | Merged theorem | Generic signed target-cross-residual telescope |
| #4913 | Merged theorem | Physical cyclic telescope and terminal-profile norm identity |
| #4914 | Merged theorem | Linear projected-forcing / residual-feedback split |
| #4915 | Merged theorem | Projected forcing = target/source commutator |
| #4916 | Merged theorem | Genuine beta-zero commutator vanishing |
| #4917 | Merged theorem | Nonnegative operator-norm forcing coefficient, zero at beta zero |
| #4918 | Merged theorem | Cross-residual commutator/feedback receiver |
| #4919 | Merged theorem | Nonexpansive target-residual feedback |
| #4920 | Merged theorem | Ordered forcing-budget telescope, fixed-start specialization |
| #4921 | Merged theorem | Cyclic terminal-profile forcing-budget receiver |

Latest theorem merge: `4b11fd20cd2bbcba5a84bec2fedafc2aaaa4e47c`. Its validated PR head is `827068e4ee47cd6ad35c2f208506ea82f817d493`; the associated run is `36528060981`. Do not confuse the merge SHA, the PR-head SHA, and a later docs-only SHA.

## 12. Lean and CI continuation rules

The pinned source definitions and explicit hypotheses remain the source of truth. Reuse canonical prefix, stage-profile, RMS, response Fubini, Schur, backward-law-response, and density/closure infrastructure; do not restart the older pointwise RMS route with its outer-energy / pointwise mismatch.

For theorem-bearing changes, inspect the entire changed module and CompileSmoke together with imports and dependent signatures. In particular:

- Local instances do not cross import boundaries; reintroduce named local instances when needed.
- Prefer compact aliases, `calc`, and explicit `congrArg` over broad dependent rewriting. The #4921 norm bridge uses `congrArg` followed by `simpa only [norm_neg]`; target idempotence at a vector uses `ContinuousLinearMap.comp_apply` explicitly.
- Imported namespaces can shadow familiar lemmas. Use the intended qualified declaration, such as `_root_.add_le_add`, where needed. The #4920 explicit `List.rec` budget preserves the intended empty/cons equations and the source-preflight-compatible definition form.
- Keep arithmetic simplification local. Preserve `K_pin(source,target)` and the physical transpose convention separately; do not infer response symmetry.
- Do not use arbitrary L2 pointwise representatives, unproved measure/carrier identifications, positive-beta projection commutativity, volume-dependent Cauchy multiplicities, or arbitrary factors two.

Classify theorem CI only at the fresh exact PR head. Check the completed `PR Lean Fast Check` result and the matching `chatgpt-ci-receipt/PR Lean Fast Check`; the receipt is a completion notification, not a substitute for the run. Require the appropriate mergeable state before merging an open PR.

The current cache workflow separates pinned `.lake/packages` from `.lake/build`, restores project artifacts from the relevant base/PR scope, and uses dependency-aware `lake build`. GitHub PR CI disables only the duplicate direct Lean elaboration pass. Toolchain/manifest changes still invalidate the pinned dependency cache.

README / ROADMAP-only changes do not match the Fast Check path filters. Do not dispatch Strict Lean or a cache-warming run for those changes. Verify the docs-only diff and links; do not label an intentionally absent Lean run as a theorem failure or synthesize a success receipt.

## 13. Restart sequence

Freshly read `formal/real-hilbert-uniform-coercive-strong-limit`. Expect theorem baseline `4b11fd20cd2bbcba5a84bec2fedafc2aaaa4e47c` unless a later theorem merge exists; distinguish any intervening docs or CI commits.

Start from [the #4921 cyclic forcing receiver][cyclic-forcing], [the #4919 nonexpansive step][nonexpansive-step], [the #4911 classification][profile-classification], and [the #4902 beta-small Schur receiver][beta-small-schur]. Check their exact hypotheses before designing the next theorem.

Retain the actual `suffix ++ pre` trajectory, its bounded representatives, and the residual-energy identities. The next new theorem should close F1, the analytic forcing comparison with its domain and orientation, then F2, the semantic terminal recurrence. F3 remains a separate strict renewal requirement. Only after F1--F4 close does the thermodynamic / continuum stage become the active frontier.

```text
CURRENT: exact cyclic terminal-profile forcing receiver
NEXT:    beta-small analytic forcing-to-profile comparison
THEN:    actual terminal recurrence -> existing #4902 Schur bound
PLUS:    strict renewal contraction
GOAL:    delta(beta) < 1/6 -> positive-beta physical transfer gap
LATER:   thermodynamic and continuum OS / Wightman construction
```

## Primary theorem modules

These relative links resolve inside the selected repository branch. Use the exact theorem checkpoint above when a stable source snapshot is needed.

[source-semantics]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceUpdateSemantics.lean
[source-quantitative]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceUpdateQuantitative.lean
[prefix-representatives]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicPrefixRepresentatives.lean
[step-carrier]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceStepCarrier.lean
[step-residual]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceStepResidual.lean
[stage-quantitative]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceStepQuantitative.lean
[profile-classification]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceStepProfileClassification.lean
[signed-telescope]: MGAP4D/MathlibAnalytic/RealHilbertProjectionSweepTargetCrossResidualTelescoping.lean
[cyclic-telescope]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTargetCrossResidualTelescoping.lean
[linear-split]: MGAP4D/MathlibAnalytic/RealHilbertProjectionSweepTargetCrossResidualLinearDecomposition.lean
[commutator-forcing]: MGAP4D/MathlibAnalytic/RealHilbertProjectionSweepTargetSourceCommutatorForcing.lean
[zero-commutator]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateTargetSourceCommutator.lean
[commutator-coefficient]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetSourceCommutatorCoefficient.lean
[cross-receiver]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetCrossResidualCommutatorFeedbackReceiver.lean
[nonexpansive-step]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetResidualCommutatorNonexpansiveStep.lean
[forcing-telescope]: MGAP4D/MathlibAnalytic/RealHilbertProjectionSweepTargetResidualForcingBudgetTelescope.lean
[cyclic-forcing]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTerminalProfileForcingBudget.lean
[beta-small-schur]: MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointTerminalProfileBetaSmallSchurFeedback.lean
