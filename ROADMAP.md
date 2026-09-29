# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-29 JST

| Item | Value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique authoritative theorem-carrier | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing baseline | `9ca5660a27bf84458f6db30c935ce43d920149e0` |
| Latest theorem merge | [PR #4932](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4932), genuine joint double-projection leakage |
| #4932 validated PR head | `4a8416abe169958d688f0b30315c02cfaade0115` |
| #4932 validation | [PR Lean Fast Check 36562217356](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36562217356): completed / success; matching exact-head receipt: success |
| Prerequisite #4931 merge | `9ca9cb81a8ced1fce20d1301a365f054e2bc5416` |
| #4931 validated PR head | `d7bc3f152a649b5d6c13f6800ed9c309493b25ee` |
| #4931 validation | [PR Lean Fast Check 36561725585](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36561725585): completed / success; matching exact-head receipt: success |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

[Authoritative branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Overview](README.md)

`main` is not theorem authority. README / ROADMAP on `main` are documentation mirrors, with theorem links pinned to the authoritative snapshot. A docs-only merge may advance either branch pointer without changing the theorem-bearing baseline. Do not confuse a merge SHA, its validated PR-head SHA and a later docs-only SHA.

Authority order: fresh exact theorem-carrier SHA; formal Lean artifacts; README / ROADMAP; exact-head CI evidence; history / memory. Re-observe the branch before continuing; this table records a checkpoint rather than predicting a moving HEAD.

## 0. Current frontier

The finite-volume Wilson / OS / physical-transfer framework, exact beta-zero gap and response / RMS / Schur infrastructure remain available. The positive-beta finite-volume physical transfer gap and the continuum Yang--Mills existence and mass-gap theorem are not yet closed.

**The frontier after #4932 is no longer the joint-leakage numerator identification.** The following are now proved:

```text
canonical mean in genuine joint L2 = actual CondExpL2
canonical residual vector = [F] - P_target [F]
canonical variance = ofReal(||[F] - P_target [F]||^2)

vacuum-integrated fixed-boundary source leakage
  = ofReal(||P_target [F] - P_source(P_target [F])||_joint^2)

on the existing strict cutoff, for actual g = P_source f in the bounded core:
  ofReal(||P_target g - P_source(P_target g)||^2)
    <= (2^-1 * Gamma(source,target)) * ofReal(||g - P_target g||^2).
```

The immediate work is the **real square-root coefficient and its correctly oriented physical-envelope comparison**. This supplies the existing source-fixed leakage receiver, then the actual suffix/pre profile assembly. Strict renewal contraction remains a separate requirement after that connection.

Do not reopen the older missing steps: the cyclic carrier, bounded intermediate representatives, exact stage residuals, profile classification, the bounded-core quantifier adapter, conditional iid normalization, stationary variance realization, canonical mean identification, and genuine joint numerator bridge are all present.

## 1. Notation, domains and the physical gap receiver

The physical declarations carry `H N : Nat`, `hN : 0 < N`, `beta : Real`, and `hbeta : 0 <= beta`. Below these parameters are suppressed, not removed.

```text
P_e        = genuine joint one-link CondExpL2
B_c        = genuine color-block conditional expectation
S_c        = one complete canonical same-color one-link sweep
L_c(f)     = exact one-pass path loss
D_c(f)     = ||S_c f - B_c f||^2

L(f)       = (1/6) * sum_c L_c(f)
Dmean(f)   = (1/6) * sum_c D_c(f)
Lterm(f)   = (1/6) * sum_c L_c(S_c f)
Dnext(f)   = (1/6) * sum_c D_c(S_c f)
r_t(x)     = x - P_t x
ell_(d,t)(g) = P_t g - P_d(P_t g).
```

Here `d` denotes source, `t` target, and `s > 1` the cutoff parameter. Keep these roles separate.

The retained exact identities include

```text
E_6sp(f) = L(f) + Dmean(f)
FullSweepMean(f) = MeanProjectedNormSq(f) + Dmean(f)
Dmean(f) = Lterm(f) + Dnext(f).
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

The objective is a volume-independent positive-beta interval and certified coefficient, not merely a lattice-size-dependent finite-dimensional estimate. This perturbative receiver is distinct from the exact endpoint theorem `gap_0 = 1`.

## 2. Retained foundation — no reconstruction needed

### Exact beta-zero and common-fixed-space geometry

PRs #4887--#4889 transport pair-Haar commutation to the genuine beta-zero carrier and prove `S_c,0 = B_c,0`, hence zero sweep/block defect. PR #4890 identifies the common fixed geometry at all allowed beta:

```text
(forall e in color c, P_e x = x) <-> B_c x = x
S_c x = x <-> B_c x = x.
```

At positive beta this does not imply pairwise commutativity or `S_c = B_c`. PR #4891 identifies the defect with the terminal block residual. PRs #4892--#4893 give the exact energy/vector renewal.

### Cyclic second visit and original/terminal profiles

Fix the canonical duplicate-free split

```text
canonicalList = pre ++ target :: suffix
x0 = P_target (sweep pre f)
cyclicSources = suffix ++ pre.
```

PRs #4894--#4899 give the genuine cyclic second-visit carrier, terminal representative and exact off-diagonal source set. In the fixed-color fiber,

```text
(suffix ++ pre).toFinset = Finset.univ.erase target.
```

The order remains exactly `suffix ++ pre`. The terminal profile satisfies

```text
(1/6) * sum_e terminalProfile(e)^2 = Lterm(f).
```

PRs #4905--#4907 provide bounded concrete representatives at every actual prefix and update, with the vector identity

```text
x_after = P_source x_before
sourceResidual = x_before - x_after.
```

PR #4911 uses the existing #4856 unique-stage API to identify the actual squared source residual with `originalProfile(source)^2` for `source in suffix`, and with `terminalProfile(source)^2` for `source in pre`. PR #4910 was closed without merge as redundant; it is not a theorem milestone.

### Response, signed telescope and nonexpansive budget

The exact full/direct/response and negative transposed-law-response identities are retained. PRs #4904 and #4909 charge their direct/backward components to the exact stage-residual carrier, preserving Harnack and pin-free coefficients. Those estimates do not license a pointwise-in-background RMS majorization or an arbitrary sum-of-norms bound.

PRs #4912--#4919 establish the signed cross-residual telescope, its commutator split and nonexpansive target-residual feedback. In particular,

```text
C(t,d) = P_t P_d - P_d P_t
r_t(P_d x) = -C(t,d)(P_t x) + r_t(P_d(r_t(x)))
||r_t(P_d(r_t(x)))|| <= ||r_t(x)||
c_comm(t,d;0) = 0.
```

Endpoint vanishing alone is not a uniform positive-beta estimate. The active route below preserves cancellation through source-fixed leakage instead of asserting

```text
c_comm * ||P_t x|| <= smallKernel * ||x - P_d x||
```

without proof.

PRs #4920--#4921 define the ordered budget

```text
Budget([],x) = 0
Budget(d :: rest,x) = forcing(d,x) + Budget(rest,P_d x)
```

and connect it to `terminalProfile(target) <= Budget(suffix ++ pre,x0)` under the stated step hypothesis.

## 3. Bounded-core quantifier adapter — CLOSED in #4923

The original #4921 general receiver quantified its analytic step over the ambient joint L2 space. The representative estimates lived on the bounded concrete core. This mismatch is now resolved, not left to an unstated extension.

#4923 compares existing budgets only at actual before-source states in displayed list splits. It uses the exact residual-norm increment to reuse the universal telescope, then compares to the analytic forcing budget along `suffix ++ pre`. Existing core invariance and cyclic off-diagonal geometry discharge the domain conditions.

The physical analytic input now needs only

```text
x in boundedConcreteCore
source.val != target.val.
```

Do not extend a bounded-core inequality to all L2 implicitly. Conversely, do not rebuild a universal receiver just to use the present route: its correct invariant-domain receiver is already available.

Source: [PR #4923](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4923).

## 4. Source-fixed leakage to source-residual forcing — CLOSED implication in #4924

For target projection `P` and source projection `Q`, set

```text
z = Q x
r = z - P z
y = x - Q x
ell = P z - Q(P z).
```

The exact signed Hilbert pairing is

```text
||r||^2 = <r, x - P x> + <ell, y>.
```

If `k >= 0` and `||ell|| <= k * ||r||`, it implies

```text
||Q x - P(Q x)|| <= ||x - P x|| + k * ||x - Q x||.
```

The zero-residual case is handled separately. There is no projection-order swap, arbitrary factor two, or finite-cardinality loss. The physical specialization applies to source-fixed bounded-core inputs and feeds #4923 with forcing

```text
forcing(source,x) = K(source,target) * ||x - P_source x||.
```

The implication is proved. The remaining task is to provide its real coefficient from the now-proved #4932 squared estimate and relate it to the physical envelope.

Sources: [generic signed pairing][source-fixed-hilbert], [PR #4924 physical receiver](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4924).

## 5. Ordered response and exact source-pair normalization — #4925--#4930

### One source-invariant representative and cancellation

#4925 supplies one bounded strongly measurable representative of the actual `P_d f` that is invariant under replacing the right source link. It is chosen before all target choices.

#4926 cancels the direct branch exactly on such representatives:

```text
fullDifferenceL2 = responseL2.
```

This retains the signed cancellation before estimates; it is not a factor-two triangle bound and does not assume different-fiber projection commutativity.

### The ordered coefficient is already finite

#4927 retains the exact ordered kernel entry under vacuum integration. Abbreviate its ENNReal coefficient by

```text
Gamma(d,t) = ofReal(K_pin(t,d)^2) * C_RMS(s,beta)
A(d,t)     = (2 : ENNReal)^(-1) * Gamma(d,t).
```

`C_RMS` is the existing fixed-background second-mean RMS target-majorant coefficient. The exact declaration is `periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient`; its `_ne_top` theorem proves finiteness under

```text
s > 1
beta >= 0
beta <= CanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff(s).
```

No stronger shell cutoff is introduced. The coefficient is independent of the observable and outer boundary. Its entry is `K_pin(target,source)`, not `K_pin(source,target)`; its comparison with the physical envelope remains to be proved.

The resulting bound originally had a vacuum-integrated **source-pair** norm on its left and genuine joint target-residual energy on its right. #4932 now supplies the precise missing numerator bridge.

### Actual pair law, iid factor two and stationarity

#4928 expresses the source-pair full difference through the literal kernel-section target mean and actual current-value source conditional law, with no auxiliary distinguished-source ambiguity.

#4929 proves exact conditional independent-pair normalization:

```text
pairEnergy = 2 * conditionalVarianceEnergy.
```

This factor two is an equality from iid variance normalization. It is not an inequality loss to be removed informally. The identity is available on the bounded concrete domain before imposing source invariance for the response bound.

#4930 proves measurability and boundedness of the actual target mean and identifies the actual source average. Source stationarity then gives

```text
conditionalVarianceEnergy = fixedBoundaryLeakageEnergy.
```

Consequently the vacuum-integrated fixed-boundary energy retains exactly `2^-1 * Gamma(d,t)`. No extra Harnack, density or cardinality factor is introduced at this normalization step.

Sources: [ordered response and finite coefficient][ordered-response], [exact conditional pair variance][pair-variance], [stationary source residual][stationary-variance].

## 6. Canonical mean and genuine joint numerator — CLOSED in #4931--#4932

### 6.1 Canonical mean identification

For bounded strongly measurable `F`, write `[F]` for the existing genuine joint L2 embedding and `M_t(F)` for the pulled-back canonical mean. #4931 explicitly proves retained-sigma measurability. It then uses orthogonal-projection Pythagoras and the already-proved reverse residual bound:

```text
||f - m||^2 = ||f - P_t f||^2 + ||P_t f - m||^2
||f - m||^2 <= ||f - P_t f||^2
  => m = P_t f.
```

This gives

```text
[M_t(F)] = P_t [F]
canonicalResidualL2_t(F) = [F] - P_t [F]
canonicalVariance_t(F) = ofReal(||[F] - P_t [F]||^2).
```

The generic uniqueness lemma needs no finite-measure hypothesis. The physical identities hold at every `beta >= 0` on the bounded strongly measurable core, without a cutoff, source-invariance or remote-separation premise.

Useful declarations in namespace `GroundStateCanonicalMean`:

```text
canonicalMean_stronglyMeasurable_retained
canonicalMeanL2_eq_condExpL2
condExpL2_coeFn_eq_canonicalMean
canonicalResidualL2_eq_condExpResidual
canonicalVariance_eq_condExpResidualNormSq.
```

Source: [canonical mean / CondExpL2][canonical-mean].

### 6.2 Transport equality through the actual source update

#4932 first identifies the canonical target mean with the literal fixed-boundary target mean under the physical vacuum / actual kernel-section disintegration. It then transports a.e. equality through source resampling using exact source heat-bath stationarity and `Measure.ae_ae_of_ae_comp`.

Thus the literal source projection of the target mean agrees a.e. with the canonical source mean of the canonical target mean. The order is always `P_d(P_t [F])`. No claim `P_d P_t = P_t P_d` is made.

Using the existing variance disintegration and #4931,

```text
lintegral_C fixedBoundaryLeakageEnergy(d,t,F;C) dnuVac
  = ofReal(||P_t [F] - P_d(P_t [F])||_joint^2).
```

This identity holds for every bounded strongly measurable `F`, all `beta >= 0`, and arbitrary `d,t`, including equal links. Source invariance and the cutoff are used only for the following inequality, not for the identity.

### 6.3 The squared bound applies to actual source updates

Under the existing strict cutoff, for `t != d` and a source-invariant representative `F`, put `g = [F]`. Then

```text
ofReal(||ell_(d,t)(g)||^2)
  <= A(d,t) * ofReal(||g - P_t g||^2).
```

For every `f` in the bounded concrete core, #4932 applies this to the actual `g = P_d f`, with a single representative selected before all off-diagonal targets:

```text
ofReal(||P_t(P_d f) - P_d(P_t(P_d f))||^2)
  <= A(d,t) * ofReal(||P_d f - P_t(P_d f)||^2).
```

Useful declarations in namespace `GroundStateSourceFixedPairEnergy`:

```text
canonicalMean_ae_eq_targetMean
sourceProjection_congr_ae
sourceProjectedTargetMean_ae_eq_canonicalDoubleMean
fixedBoundaryLeakageEnergy_vacuum_eq_jointLeakageNormSq
jointLeakage_norm_sq_le_half_orderedCoefficient_of_sourceInvariant
sourceUpdate_jointLeakage_norm_sq_le_half_orderedCoefficient.
```

Source: [genuine joint leakage][joint-leakage].

## 7. Next theorem units and completion criteria

### F1. Real norm coefficient — OPEN, immediate interface

Start from #4932's actual-source-update inequality and #4927's existing coefficient finiteness. Introduce a suitable real coefficient, naturally

```text
k(d,t) = sqrt(A(d,t).toReal).
```

Prove nonnegativity and the ENNReal-to-real / square-root conversion on the exact existing cutoff, obtaining

```text
||ell_(d,t)(P_d f)|| <= k(d,t) * ||P_d f - P_t(P_d f)||.
```

Do not merely replace `ofReal` by real arithmetic. Preserve finiteness, the exact half coefficient and the zero-residual case. No strictly positive residual is an admissible new blanket premise.

For the #4924 receiver, instantiate the estimate on source-fixed bounded-core `g` using `f = g` and `P_d g = g`, or apply the single-updated-input Hilbert theorem directly along the invariant trajectory. This is an interface specialization, not a need to reconstruct the source-invariant representative.

**Completion:** a formally checked real norm estimate on the required bounded-core domain, not just a proposed square root in documentation.

### F2. Physical-envelope domination — OPEN

Relate `k(source,target)` to the actual envelope certified for the #4902 receiver. The ordered coefficient contains `K_pin(target,source)`, whereas the physical transpose action is

```text
(K_phys^T v)(i) = sum_j K_phys(j,i) * v(j).
```

The needed comparison must therefore name both indices and prove the relevant domination, with all RMS / half factors retained. Do not infer kernel symmetry or transpose compatibility from similar names.

If the existing envelope cannot be used without loss, certify the row/column bounds and cutoff of the new envelope instead of borrowing an unrelated `q_phys`. Do not freeze a numerical positive-beta interval before this coefficient comparison is closed.

**Completion:** an explicit, volume-uniform, correctly oriented coefficient comparison with the receiver's certified hypotheses.

### F3. Actual terminal recurrence and beta-small Schur bound — OPEN

Feed F1--F2 into #4924's source-residual forcing and #4923's bounded-core cyclic receiver. Reuse the exact `suffix ++ pre` order and #4911's original/terminal source-profile classification to prove

```text
T <= K_phys^T O + K_phys^T T.
```

This is still an open **semantic premise for the actual profiles**. The receiver in #4902 is already proved: under its certified cutoff and this premise it gives

```text
(1-q_phys(s,beta))^2 * Lterm <= q_phys(s,beta)^2 * L
q_phys(s,0) = 0.
```

Retain the external `q_phys^2` factor and exact six-color normalization. The older coefficient-one receiver #4898 is weaker and should not replace this one unnecessarily. Prove `1-q_phys > 0` before dividing to obtain an explicit `Lterm <= eta(beta) * L`.

**Completion:** the actual-profile premise is discharged and #4902 is applied without new carrier or pointwise-majorization assumptions.

### F4. Strict renewal contraction — OPEN, separate requirement

Prove a volume-uniform bound

```text
Dnext <= rhoDefect(beta) * Dmean
rhoDefect(beta) < 1,
```

or an equivalent positive renewal inequality

```text
kappa(beta) * Dmean <= Lterm
kappa(beta) > 0.
```

Use the exact renewal `Dmean = Lterm + Dnext`. Mere monotonicity, nonexpansive one-step feedback and qualitative cyclic-projection convergence do not provide the required strict uniform constant.

**Completion:** a certified positive renewal constant, not only an upper bound for terminal path loss.

### F5. Defect margin and positive-beta finite-volume gap — OPEN

After F3 and F4, the intended coefficient-preserving combination is

```text
(1-q_phys)^2 * ((1-rhoDefect) * Dmean) <= q_phys^2 * L.
```

This is a planned assembly after its premises are proved, not a claim that those premises are currently available. Establish all positivity conditions, use the existing physical-sector energy control, and prove

```text
Dmean(f) <= delta(beta) * ||f||^2
0 <= delta(beta) < 1/6.
```

Extend bounded-core estimates through the established density / continuity infrastructure where the full-carrier receiver requires it. Then apply the existing physical transfer-gap theorem, with the complete volume-independent interval and sector assumptions recorded.

### F6. Thermodynamic and continuum construction — downstream OPEN

Advance compatible finite-volume embeddings/restrictions, limiting vacuum control, the thermodynamic state and transfer/semigroup compatibility. Prove that the gap persists on the correct limiting carrier.

The later continuum stage includes the Euclidean field limit, continuum OS axioms, reflection-positive reconstruction, strongly continuous time translations, a self-adjoint Hamiltonian, vacuum/sector identification and the transfer-to-Hamiltonian-gap bridge leading to Wightman reconstruction.

A finite-volume gap alone is not the continuum theorem. These are constructive downstream objectives, not consequences already obtained from #4932.

## 8. Milestone ledger

These theorem contributions are included in the checkpoint above. Docs and CI milestones are explicitly separated from theorem-bearing work.

| PR | Classification | Contribution |
| --- | --- | --- |
| #4900 | Docs | README / ROADMAP checkpoint through #4899 |
| #4901 | Theorem | Actual cyclic source-update semantic identities |
| #4902 | Theorem | Beta-small transpose Schur receiver; zero-beta endpoint |
| #4903 | CI infrastructure | Canonical-base cache reuse |
| #4904 | Theorem | Quantitative cyclic direct/backward/response estimates |
| #4905 | Theorem | Bounded representatives at every cyclic prefix |
| #4906 | Theorem | Bounded before/after actual source-step carrier |
| #4907 | Theorem | Source residual = trajectory residual, vector and energy |
| #4908 | CI infrastructure | Split dependency/project caches; remove duplicate direct elaboration |
| #4909 | Theorem | Quantitative costs charged to exact stage-residual energy |
| #4910 | Closed, NOT merged | Redundant unique-stage surface; reuse #4856 |
| #4911 | Theorem | Exact original/terminal source-profile classification |
| #4912--#4913 | Theorems | Generic signed telescope and actual terminal-profile norm identity |
| #4914--#4915 | Theorems | Linear split and projected commutator forcing |
| #4916--#4918 | Theorems | Genuine beta-zero vanishing and commutator coefficient/receiver |
| #4919 | Theorem | Nonexpansive target-residual feedback |
| #4920--#4921 | Theorems | Ordered forcing telescope and cyclic terminal receiver |
| #4922 | Docs | Previous authoritative checkpoint through #4921 |
| #4923 | Theorem | Actual-trajectory / bounded-core quantifier adapter |
| #4924 | Theorem | Exact signed leakage pairing and source-residual forcing |
| #4925 | Theorem | One source-invariant bounded representative of the actual update |
| #4926 | Theorem | Exact direct cancellation on source-invariant representatives |
| #4927 | Theorem | Ordered vacuum response bound and finite coefficient |
| #4928 | Theorem | Actual kernel-section source-pair energy realization |
| #4929 | Theorem | Exact conditional iid factor-two normalization |
| #4930 | Theorem | Stationary fixed-boundary source residual and half coefficient |
| #4931 | Theorem | Canonical mean = genuine CondExpL2; exact residual / variance |
| #4932 | Theorem | Genuine joint numerator identity and ordered squared leakage estimate |

The former #4921 checkpoint was `4b11fd20cd2bbcba5a84bec2fedafc2aaaa4e47c`; it is historical, not current. The detailed earlier account is retained in the [#4922 documentation snapshot](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b870c3fc00b2575089fcc38d91c9b69d783755ec/ROADMAP.md). The older [main documentation through #4869](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c6d9c2edc2375c6064eea2fefd28da09d9b99739/README.md) is also a historical snapshot, not the current frontier.

## 9. Validation evidence and Lean continuation notes

### Current theorem evidence

#4931's final exact head is `d7bc3f152a649b5d6c13f6800ed9c309493b25ee`; run `36561725585` and its matching completion receipt are successful. Its actual build artifact records the theorem and CompileSmoke success. #4932's final head is `4a8416abe169958d688f0b30315c02cfaade0115`; run `36562217356` and its matching receipt are successful, with the prerequisite and new theorem/smoke modules built.

The new contribution is two modules in #4931 and two in #4932, 551 lines in total. Existing dependency lint warnings remain; no new-module Lean errors or warnings were present in these successful logs. These are formal build records, not a claim of independent external review.

On a theorem change, inspect the whole module and CompileSmoke, imports, dependent signatures and pinned mathlib APIs. If aggregate workflow metadata and actual build diagnostics disagree, reconcile the exact SHA/run/artifact rather than accepting a success label alone. A receipt is a completion notification, not a replacement for proof checking.

### Reusable elaboration lessons from #4931

- `condExpL2` returns a measurable-subspace value. Use explicit `.1` when the ambient L2 vector is required.
- Keep the intended ambient measurable-space instance unambiguous. A local measurable-space alias can shadow it; retained-sigma measurability must be shown for the correct domain.
- For the retained comap sigma-algebra, the definitional measurable-preimage witness `⟨s, hs, rfl⟩` avoids guessing an unrelated convenience lemma.
- Set `(𝕜 := ℝ)` explicitly when using `inner_condExpL2_eq_inner_fun` in the real Hilbert proof.
- Carry a.e. identities through `Lp.ext`, `Lp.coeFn_sub`, measure-preserving/absolute-continuity transport and exact stationary kernel composition. Never promote them to arbitrary pointwise identities.

Retain the earlier conventions: local instances do not propagate across imports; use focused `calc`, `congrArg`, `simpa only` and explicit `ContinuousLinearMap.comp_apply` rather than broad dependent rewriting. Disambiguate shadowed arithmetic lemmas when necessary. Preserve coefficient index order, finite ENNReal inverses and the physical transpose convention.

### Docs-only work and cache policy

Pinned Lean / mathlib, manifests, theorem sources and workflows are unchanged by this documentation refresh. The authoritative workflow retains separate pinned dependency and project caches and dependency-aware `lake build`; only the duplicate direct elaboration pass is disabled in PR CI.

README / ROADMAP-only changes do not require another Lean proof run. Check the docs-only diff, Markdown references, factual checkpoint and theorem links. Do not dispatch Strict Lean or cache warming, and do not manufacture a theorem receipt for an intentionally absent docs-only run.

Update `main` by copying only these documentation files, with links to the authoritative theorem snapshot. Never merge the theorem branch wholesale into `main` to make the README visible, and never treat the docs mirror as a second theorem carrier.

## 10. Restart sequence

Freshly observe `formal/real-hilbert-uniform-coercive-strong-limit`. The theorem checkpoint recorded here is `9ca5660a27bf84458f6db30c935ce43d920149e0`; classify any later commits as theorem, docs or infrastructure before choosing the next proof input.

Start with [#4932's genuine leakage theorem][joint-leakage] and [#4927's finite ordered coefficient][ordered-response]. Then read [#4924's Hilbert implication][source-fixed-hilbert] and its physical receiver, #4923's bounded-core cyclic receiver, #4911's profile classification and #4902's beta-small Schur receiver. Match their domains, indices and cutoff hypotheses before composition.

Do not re-prove the canonical mean identity, the iid factor two, source stationarity or the numerator disintegration. Do not restart the older pointwise RMS route with its outer-energy / pointwise mismatch. Keep the actual `suffix ++ pre` trajectory and coefficient-preserving receiver chain.

```text
CURRENT: exact genuine joint leakage numerator + ordered squared bound Gamma/2
NEXT:    F1 real norm conversion; F2 physical-envelope domination
THEN:    F3 actual terminal recurrence -> existing beta-small Schur bound
PLUS:    F4 strict renewal contraction / positive renewal lower bound
GOAL:    F5 delta(beta) < 1/6 -> positive-beta physical transfer gap
LATER:   F6 thermodynamic and continuum OS / Wightman construction
```

## Primary theorem sources

The links below use the exact theorem snapshot, so they are valid from both the authoritative documentation and the `main` mirror.

[source-fixed-hilbert]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/RealHilbertProjectionSourceFixedLeakage.lean
[ordered-response]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedIntegratedResponse.lean
[pair-variance]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFullDifferenceConditionalVariance.lean
[stationary-variance]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedPairVariance.lean
[canonical-mean]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalMeanCondExpIdentification.lean
[joint-leakage]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedJointLeakage.lean
