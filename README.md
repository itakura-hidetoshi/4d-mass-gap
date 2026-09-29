# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Current result — through merged PR #4932:** the canonical fiber mean is exactly the genuine joint conditional expectation, and the vacuum-averaged fixed-boundary leakage energy is exactly the genuine joint double-projection norm squared. The existing ordered response estimate now bounds that norm with the exact coefficient `Gamma(source,target) / 2` on actual source-updated bounded-core vectors.

**Next:** convert this ENNReal squared estimate to a real norm estimate, prove domination by the certified physical envelope with the correct index orientation, and feed the existing source-fixed leakage / cyclic-profile receivers. The actual terminal recurrence and strict renewal contraction remain to be proved.

## Authority checkpoint — 2026-09-29 JST

| Item | Authoritative value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing baseline | `9ca5660a27bf84458f6db30c935ce43d920149e0` — merged [PR #4932](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4932) |
| #4932 validated exact PR head | `4a8416abe169958d688f0b30315c02cfaade0115` |
| #4932 exact-head validation | [PR Lean Fast Check 36562217356](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36562217356): completed / success; matching receipt: success |
| #4931 prerequisite head | `d7bc3f152a649b5d6c13f6800ed9c309493b25ee` |
| #4931 exact-head validation | [PR Lean Fast Check 36561725585](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36561725585): completed / success; matching receipt: success |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

[Authoritative branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Detailed roadmap](ROADMAP.md) · [Lean modules at this theorem checkpoint](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic)

The default branch `main` is **not** theorem authority. The README / ROADMAP there are documentation mirrors; they do not move the Lean development to `main`. The source links below deliberately resolve to the exact authoritative theorem snapshot even when these documents are read on `main`.

A later docs-only commit may advance a branch pointer without advancing the theorem-bearing baseline. The CI runs above validate their stated PR heads, not a later documentation commit. Authority order: fresh exact theorem-carrier SHA; formal Lean artifacts at that SHA; README / ROADMAP; exact-head CI evidence; history / memory.

## Scope and current boundary

The repository develops the finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer framework, the **exact beta-zero physical transfer gap of 1**, and the response, RMS, genuine conditional-expectation and bidirectional Schur machinery used below.

A complete continuum four-dimensional Yang--Mills existence and mass-gap theorem is **not yet established here**. The active finite-volume objective is a volume-uniform positive-beta comparison between a noncommutative same-color one-link sweep and the genuine color-block projection. The recent joint-leakage theorem closes a concrete analytic identification in that route; it does not by itself supply the remaining contraction constants.

| Layer | Status at #4932 |
| --- | --- |
| Exact renewal, cyclic second visit and off-diagonal source set | Proved |
| Bounded representatives, exact stage residuals and suffix/pre profile classification | Proved |
| Signed telescope, nonexpansive feedback and ordered forcing budget | Proved |
| Bounded-core / actual-trajectory receiver, without an ambient-L2 analytic premise | Proved in #4923 |
| Source-fixed leakage implies source-residual forcing | Proved implication in #4924 |
| One source-invariant representative for the actual source update; exact direct cancellation | Proved in #4925--#4926 |
| Ordered vacuum response coefficient and its finiteness on the existing strict cutoff | Proved in #4927 |
| Actual kernel-section pair energy, exact iid factor two and stationary source variance | Proved in #4928--#4930 |
| Canonical mean = genuine joint CondExpL2; exact canonical residual / variance | Proved in #4931 |
| Fixed-boundary leakage = genuine joint double-projection norm squared | Proved in #4932 |
| Genuine squared leakage estimate with exactly half the ordered coefficient | Proved in #4932 on the stated bounded-core / cutoff domain |
| Real square-root coefficient and physical-envelope domination | Open next interface |
| Actual terminal recurrence and strict next-defect contraction | Open, distinct requirements |
| `delta(beta) < 1/6` and positive-beta finite-volume physical transfer gap | Open |
| Thermodynamic limit and continuum OS / Wightman mass-gap construction | Downstream open goals |

## 1. Exact sweep geometry is retained

Let `P_e` be the genuine joint one-link conditional expectation. For spatial color `c`, let `B_c` be the genuine color-block projection and `S_c` the complete canonical same-color one-link sweep. Write

```text
D_c(f)   = ||S_c f - B_c f||^2
Dmean(f) = six-color average of D_c(f)
L(f)     = six-color average of the original sweep path loss
Lterm(f) = six-color average of the second-sweep path loss
Dnext(f) = six-color average of D_c(S_c f).
```

The exact renewal and terminal-profile normalization are

```text
Dmean(f) = Lterm(f) + Dnext(f)
(1/6) * sum_e terminalProfile(e)^2 = Lterm(f).
```

For `canonicalList = pre ++ target :: suffix`, the actual between-visits trajectory starts at

```text
x0 = P_target (sweep pre f)
cyclicSources = suffix ++ pre.
```

It contains every other same-color link exactly once, in that order. A source in `suffix` contributes its original-profile residual; a source in `pre` contributes its terminal-profile residual. This geometry and its bounded representatives are already available; they are not the next missing construction.

At beta zero, `S_c = B_c` exactly. At positive beta, equality of common fixed spaces does not imply commutativity or equality of these operators.

## 2. The active route uses source-fixed leakage, not an unsupported commutator substitution

PRs #4920--#4921 establish the ordered terminal forcing budget. PR #4923 restricts the analytic hypothesis to the actual bounded-core trajectory and off-diagonal sources, closing the previous quantifier mismatch.

PR #4924 preserves cancellation before taking norms. Put

```text
z = P_d x
r = z - P_t z
y = x - P_d x
ell = P_t z - P_d(P_t z).
```

For the self-adjoint idempotent projections, the exact Hilbert identity is

```text
||r||^2 = <r, x - P_t x> + <ell, y>.
```

Consequently, a supplied bound `||ell|| <= k(d,t) * ||r||`, with `k(d,t) >= 0`, gives

```text
||P_d x - P_t(P_d x)||
  <= ||x - P_t x|| + k(d,t) * ||x - P_d x||.
```

This is the desired source-residual cost. It does not claim that an operator-norm commutator term `c_comm * ||P_t x||` can simply be replaced by a source residual. The earlier signed telescope, commutator decomposition and beta-zero vanishing remain valid structural results.

Source: [exact signed pairing and source-residual forcing][source-fixed-hilbert].

## 3. Canonical mean = genuine conditional expectation — #4931

For bounded strongly measurable `F`, let `[F]` be its existing genuine joint L2 embedding, and let `M_t(F)` be the canonical fiber mean pulled back from the retained outer coordinates.

The retained-sigma measurability of this mean is proved explicitly; ambient measurability alone would not suffice. The existing reverse residual estimate and orthogonal-projection Pythagoras then force equality:

```text
[M_t(F)] = P_t [F]
canonicalResidualL2_t(F) = [F] - P_t [F]
canonicalVariance_t(F) = ofReal(||[F] - P_t [F]||^2).
```

These physical identities hold for every `beta >= 0` on the bounded strongly measurable core, without a high-temperature cutoff or source-invariance assumption. The generic L2 uniqueness lemma does not require a finite-measure hypothesis.

Source: [canonical mean / genuine CondExpL2 identification][canonical-mean].

## 4. Actual fixed-boundary energy = genuine joint leakage — #4932

Let `H_(d,t)(F;C)` denote the existing `fixedBoundaryLeakageEnergy` at boundary `C`, and `nuVac` the physical vacuum law. The exact numerator identity is

```text
lintegral_C H_(d,t)(F;C) dnuVac
  = ofReal(||P_t [F] - P_d(P_t [F])||_joint^2).
```

The right-hand side is on the **existing genuine joint L2 carrier**, not an auxiliary source-pair Hilbert space. The identity holds for every bounded strongly measurable `F`, every `beta >= 0`, and any source/target pair, including `d = t`.

The proof uses the existing canonical/literal mean equality under the physical vacuum and actual kernel-section laws. Exact source heat-bath stationarity and mathlib's `Measure.ae_ae_of_ae_comp` transport that equality through source resampling almost everywhere. There is no pointwise evaluation of an arbitrary L2 quotient representative and no exchange of `P_d P_t` with `P_t P_d`.

The preceding steps are retained: #4928 realizes the actual kernel-section pair energy, #4929 proves the exact factor `pairEnergy = 2 * conditionalVarianceEnergy`, and #4930 identifies that variance with the stationary fixed-boundary residual. The half coefficient below comes from this equality, not from discarding a comparison loss.

Sources: [stationary source variance][stationary-variance], [genuine joint leakage][joint-leakage].

## 5. The genuine ordered squared leakage estimate is now proved

Use the abbreviations

```text
Gamma(d,t) = ofReal(K_pin(t,d)^2) * C_RMS(s,beta)  : ENNReal
A(d,t)     = (2 : ENNReal)^(-1) * Gamma(d,t).
```

Here `C_RMS` is the already-defined fixed-background second-mean RMS target-majorant coefficient. #4927 proves `Gamma(d,t) != infinity` on the existing strict physical-sweep cutoff, with `s > 1`, `beta >= 0` and the stated physical parameters. The literal pin-free entry is **target, source**. This notation does not identify it with the physical envelope used by #4902.

For `t != d`, a source-invariant bounded strongly measurable representative gives

```text
ofReal(||P_t g - P_d(P_t g)||^2)
  <= A(d,t) * ofReal(||g - P_t g||^2).
```

In particular, for every `f` in the bounded concrete core, #4932 applies this to the **actual** update `g = P_d f`:

```text
ofReal(||P_t(P_d f) - P_d(P_t(P_d f))||^2)
  <= A(d,t) * ofReal(||P_d f - P_t(P_d f)||^2).
```

One source-invariant representative is selected before all off-diagonal targets. The source/target order, exact half coefficient and existing cutoff are preserved.

**Not yet packaged:** the corresponding real norm coefficient, its domination by the certified physical envelope, and the resulting actual cyclic terminal recurrence. Finiteness is already proved; the conversion and comparison remain the next formal interface.

Sources: [ordered coefficient and integrated response][ordered-response], [squared genuine leakage theorem][joint-leakage].

## 6. Remaining route to the physical gap

The next coefficient candidate is `sqrt(A(d,t).toReal)`. Its use must be justified from the proved finite ENNReal estimate, with the zero-residual case and nonnegativity preserved. Then prove the appropriate comparison with the physical envelope and apply the existing #4924 / #4923 receivers, rather than rebuilding the carriers.

The remaining route is

```text
real norm coefficient + correctly oriented physical-envelope domination
  -> source-residual cyclic forcing on the actual bounded-core trajectory
  -> suffix/pre profile assembly
  -> actual T <= K_phys^T O + K_phys^T T
  -> existing #4902 beta-small Schur receiver
  + strict renewal contraction or equivalent positive renewal bound
  -> Dmean(f) <= delta(beta) * ||f||^2
  -> certify 0 <= delta(beta) < 1/6
  -> existing positive-beta physical transfer-gap receiver.
```

The certified physical transpose convention is `(K_phys^T v)(i) = sum_j K_phys(j,i) * v(j)`. Given its actual semantic premise, #4902 already proves

```text
(1 - q_phys(s,beta))^2 * Lterm(f) <= q_phys(s,beta)^2 * L(f)
q_phys(s,0) = 0.
```

That is a proved implication, not a claim that its actual-profile premise is supplied by #4932. Strict renewal, for example `Dnext <= rhoDefect * Dmean` with `rhoDefect < 1`, is a separate remaining input. Prove positivity before any division.

The existing defect-margin receiver yields `(3/8) * (1/6 - delta(beta)) <= physical transfer gap`. This perturbative lower bound is distinct from the exact beta-zero result `gap_0 = 1`. Thermodynamic and continuum constructions remain downstream.

## Lean / documentation workflow

The theorem validation checkpoint above is backed by completed exact-head Fast Check runs, matching receipts and actual successful build diagnostics for the new theorem and CompileSmoke modules. These are Lean validation records, not a claim of independent external review or a completed continuum theorem.

The authoritative workflow retains pinned dependency and project caches and dependency-aware `lake build`; the duplicate direct elaboration pass is not repeated in PR CI. Inspect complete changed modules, imports, local instances and pinned APIs when repairing Lean, rather than only the reported error lines.

README / ROADMAP-only updates do not require another theorem run. Verify the two-file diff, SHA references and links; do not dispatch Strict Lean, warm caches or synthesize a theorem receipt for a documentation change. The mirrors on `main` must preserve the theorem-carrier distinction and must not merge the theorem branch into `main`.

The detailed hypothesis boundaries, milestone ledger and restart sequence are in [ROADMAP.md](ROADMAP.md).

[source-fixed-hilbert]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/RealHilbertProjectionSourceFixedLeakage.lean
[canonical-mean]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalMeanCondExpIdentification.lean
[stationary-variance]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedPairVariance.lean
[ordered-response]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedIntegratedResponse.lean
[joint-leakage]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9ca5660a27bf84458f6db30c935ce43d920149e0/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedJointLeakage.lean
