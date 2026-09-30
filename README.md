# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Current theorem status — through merged PR #4971:** the genuine two-sided one-link dynamics on the physical ground-state joint (L^2) carrier now has a strict high-temperature full-sweep loss contraction, converges to the intrinsic constant-line orthogonal projection, and satisfies an **all-(L^2) two-sided relative Poincaré inequality** with a strictly positive, volume/rank-independent coefficient on the same certified cutoff.

The new endpoint is not yet the positive-beta physical transfer-gap theorem. The #4971 right-hand side is the **unnormalized sum of all tagged two-sided one-link residuals**, so one further model-facing bridge is required: compress this estimate to a volume-free grouped two-sided spatial frame, identify the constant-line center correctly on the physical top-orthogonal right-boundary sector, and then use the already-existing twelve-spatial / physical-defect receiver.

## Authority checkpoint — 2026-10-01 JST

| Item | Authoritative value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing snapshot | `22bfe27324e374242aad7bc402a224769306a22b` — merged [PR #4971](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4971) |
| #4971 validated exact PR head | `cf43f174d76451400bb10301c6cb2549be0118b6` |
| #4971 exact-head validation | [PR Lean Fast Check 36784485909](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36784485909): completed / success; matching exact-head receipt: success |
| #4971 build | `Build completed successfully (9420 jobs)` |
| #4971 artifact | `11129237482`, `sha256:2601e587a80eeb3692f12db43fdcd90a3f1e88b465922f18a2efa4569bddde6c` |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Detailed roadmap](ROADMAP.md) · [Lean modules at the #4971 theorem snapshot](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic)

The default branch `main` is **not theorem authority**. README / ROADMAP on `main` are documentation mirrors only. A docs-only merge may advance a branch pointer without advancing the theorem-bearing mathematical baseline. Authority order is:

1. fresh exact theorem-carrier SHA;
2. formal Lean artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

## Scope and current boundary

The repository contains a large finite-volume Wilson / Osterwalder--Schrader / transfer-operator development, including the exact beta-zero physical transfer gap

```text
gap(beta = 0) = 1.
```

At positive beta, the active route is now much further downstream than the older source-fixed leakage frontier. The recent theorem chain has closed the real leakage conversion, ordered Schur recurrence, renewal contraction, genuine two-sided cross-boundary dynamics, strong convergence of the complete two-sided sweep, and the all-(L^2) relative Poincaré inequality.

A complete continuum four-dimensional Yang--Mills existence and mass-gap theorem is **not yet established here**. In particular, #4971 is not itself the final finite-volume physical transfer-gap theorem.

## What is now closed

### A. Real leakage and ordered Schur machinery — #4935--#4937

The ENNReal squared leakage estimate was converted to the exact real norm coefficient with its finite square-root normalization. The source/target orientation was kept explicit, then the actual bounded-core terminal recurrence was assembled through an ordered RMS Schur envelope with a volume-independent small-coupling cutoff.

This removed the older “real square-root coefficient / physical-envelope orientation” frontier.

### B. Renewal and full genuine joint (L^2) control — #4938--#4941

The fixed-color sweep acquired geometric loss decay and an honest renewal-tail bridge. The actual fixed-color sweep limit and uniform renewal-defect contraction were identified. Ordered defect control was then extended to the full genuine joint (L^2) carrier, followed by control of arbitrary all-link mixed-color sweep residuals.

The former requirement for a separate strict renewal hypothesis is therefore closed in this route.

### C. Volume-free one-sided relative frame — #4942--#4945

The all-right-link sweep gives a relative Poincaré estimate with the complete retained left boundary. Grouping the complete right-link family into the six canonical spatial colors yields the volume-free normalized six-color estimate

```text
((1 - 2 Q)^2 / 36) * ||f - C_left f||^2 <= E_6(f),
```

with no link-count factor. The retained projection was also identified with the coarse / Doob geometry.

An existing receiver already turns such a six-color relative frame into a physical transfer gap **if** one separately supplies a strict retained-boundary contraction. That receiver is retained, but the current two-sided route below is designed to avoid leaving that contraction as an external premise.

### D. Genuine cross-boundary two-sided kernel — #4946--#4966

The development then passed from the one-sided retained-boundary problem to actual two-sided dynamics:

- two-boundary ordered Schur envelope;
- genuine left and two-sided one-link conditional expectations;
- variance-sensitive (L^2) mean comparison from mutual Harnack bounds;
- endpoint-swap symmetry and conjugation of one-link projections;
- removal of the independent-pair factor two;
- actual kernel-section fiber identification;
- source-invariant cross-boundary target means and integrated source response;
- exact return of target variance to genuine target residual;
- source variance identified with genuine left leakage;
- genuine cross-boundary one-step (L^2) influence;
- actual left-update leakage with exact diagonal-support preservation;
- final actual two-sided one-link leakage bound with the ordered block kernel.

This is the analytic bridge that made a true two-sided recurrence possible.

### E. Two-sided dynamics and intrinsic limit — #4967--#4970

#4967 constructs the bounded-core two-sided cyclic forcing budget. #4968 closes the actual two-sided ordered terminal recurrence.

#4969 then chooses a positive volume/rank-independent cutoff on which the two-boundary Schur coefficient satisfies

```text
0 <= Q < 1/2
eta = (Q / (1 - Q))^2
0 <= eta < 1,
```

and proves, first on the bounded core and then by density/closedness on **all genuine joint (L^2)**,

```text
loss(S f) <= eta * loss(f).
```

Consequently the complete two-sided one-link sweep has geometric path-loss decay.

#4970 identifies the common fixed space of all genuine tagged two-sided one-link conditional expectations with the **intrinsic joint constant line**, defines its orthogonal projection `B`, proves `B` absorbs every tagged update and the full sweep, and establishes

```text
S^[n] f  ->  B f
```

strongly for every genuine joint (L^2) vector on the same #4969 cutoff.

### F. All-(L^2) two-sided relative Poincaré — #4971

Let

```text
P_e = genuine tagged two-sided one-link CondExpL2
B   = intrinsic joint constant-line orthogonal projection
Q   = twoBoundaryOrderedSchurCoefficient(s,beta).
```

Under

```text
s > 8,
0 <= beta,
beta <= twoBoundaryOrderedLossContractionCutoff(s),
```

#4971 proves for every genuine joint (L^2) vector `f`:

```text
(1 - 2 Q) * ||f - B f||^2
  <= sum_e ||f - P_e f||^2.
```

The coefficient is strictly positive on the same cutoff:

```text
0 < 1 - 2 Q.
```

The proof uses the all-(L^2) cross one-step estimate, exact path-loss control by the original tagged residual energy, constant-projection Pythagoras, and #4970 strong convergence to discharge the renewal tail.

Sources: [#4969 loss contraction][two-sided-loss], [#4970 constant-line convergence][constant-line], [#4971 relative Poincaré][two-sided-poincare].

## What remains before the positive-beta physical transfer gap

The current missing interface is narrower than the older retained-boundary problem.

### 1. Volume-free grouped two-sided frame

#4971 controls the **sum over all tagged links**. It must be compressed to a fixed-cardinality two-sided grouped spatial frame without introducing a factor proportional to lattice volume. The one-sided six-color argument from #4943 is the model: group by the canonical spatial colors and use only fixed finite-color Cauchy--Schwarz.

The target should be a genuine two-sided 12-spatial frame (or the already-used physical (1/8)-normalized equivalent) with a coefficient depending only on the certified small-coupling data, not on the number of links.

### 2. Constant-line center on the physical sector

#4971 is centered at the intrinsic joint constant projection `B`. To feed the physical receiver, prove the corresponding center is zero, or otherwise obtain the required lower bound for

```text
||R(Ux) - B(R(Ux))||^2
```

when `x` lies in the physical top-eigenspace orthogonal sector. This must be an actual theorem about the joint constant line and the physical right-boundary lift, not an informal identification of different carriers.

### 3. Existing physical receiver

The repository already contains the required downstream receivers:

- a conventional twelve-spatial Poincaré estimate on physical right-boundary lifts implies a six-spatial frame and the explicit transfer-gap lower bound `3 * kappa / 4`;
- the physical (1/8)-normalized two-sided twelve-spatial frame reduces exactly to the existing eight-color residual on right-boundary lifts and feeds the raw physical squared defect.

Therefore the next work should connect #4971 to these receivers rather than rebuilding transfer-operator theory.

### 4. Uniform scaling family

The #4969 cutoff and the #4971 coefficient are already volume/rank-independent for fixed `s > 8`. If the grouped-frame and physical-centering bridges introduce no volume loss, package one common positive coefficient over the scaling family and invoke the existing uniform transfer-gap receiver.

Only after this finite-volume uniform positive-beta gap is closed should the development move the active frontier back to thermodynamic / continuum OS--Wightman construction.

## What this repository does not currently claim

- #4971 does **not** by itself prove the positive-beta physical transfer gap.
- The tagged-link residual sum is **not** silently identified with a normalized 12-color frame.
- The intrinsic constant-line projection is **not** silently replaced by zero on the physical top-orthogonal sector.
- A finite-volume or uniform transfer gap is not the same as the full continuum Yang--Mills existence and mass-gap theorem.
- The exact beta-zero gap `1` remains a separate stronger endpoint theorem; the perturbative positive-beta constants need not reproduce it sharply.

## Lean / validation workflow

The #4971 checkpoint is backed by the exact PR head `cf43f174...`, successful PR Lean Fast Check run `36784485909`, the actual `9420 jobs` successful build log, CompileSmoke declarations, and the matching exact-head completion receipt.

The #4971 theorem axiom report contains the standard `propext`, `Classical.choice`, `Quot.sound` dependencies together with the repository's existing `native_decide` cardinality certificates; there is no `sorryAx`.

When repairing theorem PRs, inspect the **whole changed Lean module**, its imports, local instances, dependent signatures, and the pinned mathlib API rather than patching only the line printed by CI. Once an unchanged exact PR head is GREEN, do not rerun Strict Lean merely for reassurance.

README / ROADMAP-only changes are documentation work. Verify their two-file diff and source links; do not manufacture a theorem receipt for them.

## Milestone map since the previous docs checkpoint

| PR range | Closed layer |
| --- | --- |
| #4935--#4937 | real leakage coefficient, ordered RMS Schur envelope, actual terminal recurrence |
| #4938--#4941 | geometric renewal, fixed-color limit, full-(L^2) defect and all-link residual control |
| #4942--#4945 | all-right relative Poincaré, volume-free six-color frame, physical receiver, retained/coarse identification |
| #4946--#4954 | two-boundary Schur, two-sided projections, Harnack (L^2), swap symmetry, actual fiber laws |
| #4955--#4966 | concrete cross-boundary means/variances, genuine one-step leakage, actual two-sided leakage |
| #4967--#4968 | two-sided cyclic forcing and ordered terminal recurrence |
| #4969 | strict all-(L^2) two-sided full-sweep loss contraction |
| #4970 | intrinsic constant-line identification and strong sweep convergence |
| #4971 | all-(L^2) two-sided relative Poincaré |

For the detailed next-step sequence, see [ROADMAP.md](ROADMAP.md).

[two-sided-loss]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedLossContraction.lean
[constant-line]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedConstantLineConvergence.lean
[two-sided-poincare]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedRelativePoincare.lean
[twelve-gap-receiver]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap.lean
[twelve-frame-receiver]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialFrame.lean
