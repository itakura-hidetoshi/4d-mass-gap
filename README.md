# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Current theorem status — through merged PR #4985:** the positive-beta finite-volume physical transfer-gap route is now closed on a nonempty, volume/rank-independent high-temperature interval. The development has also placed the resulting scale-uniform top-orthogonal dynamics into one common interacting boundary Hilbert carrier and proved that the explicit gap survives any compatible common-carrier strong limit.

The current theorem-bearing endpoint is therefore no longer the grouped-frame problem. The remaining H1 work is **construction of the actual model-facing strong-limit compatibility data** needed to instantiate the already-proved limit-preservation theorem. Continuum scaling, OS reconstruction, and the final Wightman/spectral mass-gap statement remain downstream and are not claimed complete.

## Authority checkpoint — 2026-10-01 JST

| Item | Authoritative value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing snapshot | `88870c84503e22797397f7082a1cfc9b4dc36322` — merged [PR #4985](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4985) |
| #4985 validated exact PR head | `a0db6d3d4c1184a5c81d41b4766efc12aca1e6ca` |
| #4985 exact-head validation | [PR Lean Fast Check 36810743769](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36810743769): completed / success; matching exact-head receipt: success |
| #4985 build | `Build completed successfully (9678 jobs)` |
| #4985 static audit | `axiom: 0`; forbidden tokens `sorry/admit/axiom/constant` audited |
| #4985 artifact | `11139946207`; `sha256:ca6a88ee9772b1694a916a67651053164fab6960eb99b35da4f99b246601cf2d` |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Detailed roadmap](ROADMAP.md) · [Lean modules at the #4985 theorem snapshot](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic)

The default branch `main` is **not theorem authority**. README / ROADMAP on `main` are documentation mirrors only. A docs-only merge may advance a branch pointer without changing the mathematical theorem snapshot.

Authority order is fixed:

1. fresh exact theorem-carrier SHA;
2. formal Lean artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

## Scope and current boundary

The repository already contains the exact beta-zero endpoint

```text
physical transfer gap at beta = 0 = 1.
```

At positive beta, the active route now proves a uniform finite-volume physical transfer gap and transports its top-orthogonal contraction into a common interacting boundary carrier.

A complete continuum four-dimensional Yang--Mills existence and mass-gap theorem is **not yet established here**. In particular:

- #4985 proves preservation of the discrete gap **conditional on compatible strong-limit data**;
- it does not construct that strong-limit data;
- it does not by itself identify the finite one-slab top sector with the periodic OS vacuum-orthogonal sector;
- it does not construct the continuum (C_0) semigroup or Hamiltonian;
- it does not establish the final Wightman / energy-momentum mass-gap statement.

## What is now closed

### A. Two-sided tagged-link analysis — #4935--#4971

The earlier real-leakage, Schur, renewal and two-sided recurrence chain is closed.

In particular, #4969 proves on all genuine joint (L^2) the strict full-sweep loss contraction

```text
loss(S f) <= eta * loss(f),
eta = (Q / (1 - Q))^2 < 1,
```

on a volume/rank-independent high-temperature cutoff.

#4970 identifies the complete two-sided sweep fixed space with the intrinsic joint constant line and proves

```text
S^[n] f -> B f
```

strongly.

#4971 then proves the all-(L^2) tagged-link relative Poincaré inequality

```text
(1 - 2 Q) * ||f - B f||^2
  <= sum_e ||f - P_e f||^2,
0 < 1 - 2 Q.
```

These are retained dependencies and are not the active frontier.

### B. Order-robust complete two-sided sweep — #4976--#4978

Because the one-link conditional expectations do not commute, the twelve-color grouping could not be justified by silently reordering the canonical tagged-link sweep.

#4976 generalizes the #4969 strict loss contraction to **any complete duplicate-free tagged-link order**.

#4977 constructs the complete right-six + left-six grouped two-sided link order.

#4978 extends the complete-order theorem to the full #4970 geometry:

- fixed space = intrinsic constant line;
- constant projection absorbs the supplied complete order;
- iterates converge strongly to the constant projection;
- constant-centered squared norm contracts by the same two-boundary loss ratio.

This removes the noncommuting-order obstruction from G1.

### C. Left six-color transport and the genuine twelve-spatial frame — #4979--#4980

#4979 transports the existing right six-color whole-block displacement estimate across endpoint swap to the left six-color family, at the **whole-color** level rather than link-by-link.

#4980 then closes G1 with the fixed twelve-color energy

```text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f),
```

where

```text
kappa_12(s,beta)
  = (1 - sqrt(twoBoundaryOrderedLossRatio(s,beta)))^2 / 576.
```

The frame cutoff is

```text
min(
  twoBoundaryOrderedLossContractionCutoff,
  jointLeakageLossContractionCutoff
).
```

The factor (576 = 4 cdot 12^2) comes only from a fixed factor-two comparison and Cauchy--Schwarz over the **fixed twelve colors**. There is no lattice-link, volume or rank factor.

### D. Intrinsic constant center -> physical top-orthogonal sector — #4981

#4981 closes G2 without identifying spaces by name.

For a physical vector (x) in the full normalized-transfer top-eigenspace orthogonal sector, after the existing Haar-to-vacuum transform (U) and genuine right-boundary lift (R),

```text
B (R (U x)) = 0
```

and therefore

```text
||R(Ux) - B(R(Ux))||^2 = ||x||^2.
```

The proof uses the actual inner-product geometry:

- the nonnegative normalized top eigenvector lies in the full top eigenspace;
- (U) maps it to constant one;
- (R) maps that to the intrinsic joint constant-one vector;
- both maps preserve inner products.

Thus #4980 becomes a conventional twelve-spatial Poincaré inequality on the actual physical top-orthogonal right lifts.

The existing receiver then gives

```text
3 * kappa_12(s,beta) / 4
  <= physical top-eigenspace transfer gap,
```

and strict positive-beta finite-volume gap positivity on the certified interval.

### E. Explicit scale-uniform physical transfer gap — #4982

#4982 closes G4.

It chooses a smaller positive common cutoff on which

```text
twoBoundaryOrderedSchurCoefficient(s,beta) < 1/3.
```

On that interval,

```text
1/2304 <= kappa_12(s,beta),
```

so every scale satisfies the explicit uniform physical transfer-gap bound

```text
1/3072 <= physical top-eigenspace transfer gap.
```

This establishes the repository target

```text
PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
```

without lattice-volume, link-count, gauge-rank or scale-dependent loss.

### F. Scale-uniform top-orthogonal power decay — #4983

Writing

```text
q0 = 3071/3072,
```

#4983 proves for every scale (n), every positive integer (k), and every physical top-orthogonal excitation (x),

```text
||R_n|| <= q0 < 1,
||R_n^k|| <= q0^k,
||R_n^k x|| <= q0^k ||x||.
```

It also records the associated positive logarithmic discrete rate

```text
-glog(q0) = -log(3071/3072) > 0.
```

### G. Common interacting boundary carrier — #4984

#4984 begins H1.

Every finite physical top-orthogonal sector is embedded isometrically into the **same interacting infinite-product boundary (L^2) carrier** by composing:

1. the one-sided excitation boundary isometry;
2. reciprocal-vacuum transport from boundary Haar (L^2) to the actual interacting finite boundary marginal;
3. coordinate pullback into the infinite product of all finite interacting boundary marginals.

No exact coarse-graining identity between different periodic Wilson Gibbs measures is assumed.

On each exact finite-scale image range, the transported transfer powers retain exactly the same estimate

```text
||T_{n,common}^k|| <= q0^k.
```

### H. Strong-limit preservation of the uniform gap — #4985

#4985 closes the abstract H1 descent step.

If embedded finite initial vectors converge strongly in the common carrier, and the corresponding embedded evolved vectors also converge strongly, then the limit obeys

```text
||y_limit|| <= q0^k ||x_limit||.
```

It then packages a compatible limiting normed space (E), an isometric embedding of (E) into the common carrier, finite approximants, and a bounded limit operator (T). Under those explicit compatibility hypotheses,

```text
||T|| <= q0^k
```

for the selected (k)-step limit operator.

For the one-step specialization,

```text
||T|| <= 3071/3072
1/3072 <= 1 - ||T||
||T|| < 1.
```

Thus the positive finite-volume gap is now formally proven to survive **any compatible common-carrier strong limit**.

What #4985 deliberately does **not** do is construct the required approximation / strong-limit data.

## Current frontier — H1 model-facing compatibility construction

The immediate next theorem problem is no longer a gap estimate. It is to instantiate the #4985 strong-limit interface with the actual Wilson / OS continuum construction.

The required data are:

1. a concrete limiting excitation carrier (E);
2. an isometric embedding (E) into the #4984 interacting common boundary (L^2);
3. finite top-orthogonal approximants (x_n) for every (x in E);
4. strong convergence of the embedded (x_n);
5. strong convergence of the embedded one-step evolved vectors to the chosen limit operator applied to (x).

The repository already contains generic asymptotically-embedded strong-limit and common-carrier machinery. The remaining task is the **model-facing identification / approximation theorem**, not another finite-volume coercivity estimate.

A separate compatibility question must also remain explicit: the finite periodic OS vacuum-orthogonal carrier is not automatically the same object as the one-slab transfer top-orthogonal carrier. Existing mode-wise boundary-closure/eigenlift theorems may be used, but no global equality should be assumed without proof.

## Continuum-scaling caution

The uniform discrete factor

```text
q0 = 3071/3072 < 1
```

is ideal for fixed-step thermodynamic/common-carrier limits.

It must **not** be naively interpreted as a finite physical-time continuum rate when the lattice spacing (a_n 	o 0). If one used the same fixed (q_0) for (lfloor t/a_nfloor) steps at fixed (t>0), then formally

```text
q0 ^ floor(t / a_n) -> 0.
```

That would correspond to instantaneous annihilation of the excitation sector at every positive time, not a nontrivial strongly continuous continuum semigroup.

Therefore H2 must control the spacing-scaled transfer rate / rescaled dynamics rather than simply reusing the fixed one-step (q_0) as a continuum-time decay factor.

This is a downstream scaling boundary; it does not weaken the finite-volume or fixed-step H1 gap theorem.

## What this repository does not currently claim

- #4985 does not construct the actual continuum strong-limit operator.
- The finite periodic OS vacuum line is not silently identified with the one-slab transfer top eigenspace.
- Exact projective restriction between different finite periodic Wilson Gibbs measures is not assumed.
- A scale-uniform finite-volume transfer gap is not by itself the full continuum Yang--Mills mass-gap theorem.
- The fixed discrete contraction (3071/3072) is not by itself a finite physical continuum mass.
- The beta-zero exact gap (1) remains a separate sharper theorem.

## Lean / validation workflow

The current theorem checkpoint is backed by #4985 exact PR head

```text
a0db6d3d4c1184a5c81d41b4766efc12aca1e6ca
```

with:

```text
PR Lean Fast Check run 36810743769
completed / success
matching exact-head receipt: success
Build completed successfully (9678 jobs)
axiom: 0
artifact ID: 11139946207
sha256:ca6a88ee9772b1694a916a67651053164fab6960eb99b35da4f99b246601cf2d
```

The CI audit rejects `sorry`, `admit`, declaration-level `axiom`, and `constant` in the changed theorem files.

Recent Lean engineering lessons retained by the branch:

- inspect the entire changed module, not only the reported CI line;
- preserve the pinned Lean/mathlib API;
- give module-specific names to local instances when import composition can expose generated-name collisions;
- for dependent submodule carriers, make restricted `NormedSpace` instances explicit when generic conjugation lemmas need them;
- avoid broad dependent `change` / `rw` when a previously typed named theorem and a local `calc` step give a more stable proof;
- do not rerun strict validation on an unchanged exact GREEN head merely for reassurance;
- README / ROADMAP-only updates are docs work and must not be presented as new theorem validation.

## Milestone map

| PR | Closed layer |
| --- | --- |
| #4935--#4971 | real leakage -> Schur -> renewal -> two-sided recurrence -> intrinsic constant-line relative Poincaré |
| #4976 | strict two-sided loss contraction for arbitrary complete duplicate-free tagged-link order |
| #4977 | complete two-sided twelve-color grouped link order |
| #4978 | complete-order constant-line convergence and centered contraction |
| #4979 | endpoint-swap transport of whole left six-color displacement |
| #4980 | volume-free genuine two-sided twelve-spatial relative frame |
| #4981 | intrinsic constant center -> physical top-orthogonal centered norm; finite-volume positive-beta gap |
| #4982 | explicit scale-uniform coefficient (1/2304) and transfer-gap floor (1/3072) |
| #4983 | uniform (q_0^k), (q_0=3071/3072), top-orthogonal power decay |
| #4984 | isometric embedding of all finite top-orthogonal sectors into one interacting common boundary carrier |
| #4985 | strong-limit preservation of (q_0^k) and one-step gap floor (1/3072) |

For the detailed continuation sequence, see [ROADMAP.md](ROADMAP.md).

[current-frame]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialRelativeFrame.lean
[current-physical-gap]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialPhysicalTopOrthogonalGap.lean
[current-uniform-gap]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialUniformGap.lean
[current-power-decay]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferUniformTopOrthogonalPowerDecay.lean
[current-common-carrier]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryDecay.lean
[current-strong-limit]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryStrongLimit.lean
