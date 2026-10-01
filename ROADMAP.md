# MGAP4D ROADMAP

## Authority checkpoint — 2026-10-01 JST

| Item | Value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique authoritative theorem-carrier | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing snapshot | `88870c84503e22797397f7082a1cfc9b4dc36322` |
| Latest theorem merge | [PR #4985](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4985), common-carrier strong-limit preservation of the explicit uniform top-orthogonal gap |
| #4985 validated PR head | `a0db6d3d4c1184a5c81d41b4766efc12aca1e6ca` |
| #4985 validation | [PR Lean Fast Check 36810743769](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36810743769): completed / success; matching exact-head receipt: success |
| Build | `Build completed successfully (9678 jobs)` |
| Static audit | `axiom: 0`; forbidden Lean tokens audited |
| Artifact | `11139946207`; `sha256:ca6a88ee9772b1694a916a67651053164fab6960eb99b35da4f99b246601cf2d` |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Overview](README.md)

The default branch `main` is not theorem authority. README / ROADMAP there are documentation mirrors only. A docs-only merge may move a branch pointer without changing the theorem-bearing mathematical baseline.

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / memory.

## 0. Current frontier

The previous Phase G frontier is closed.

The theorem-carrier now proves, on one positive volume/rank/scale-independent high-temperature interval:

```text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f)

B (R (U x)) = 0

3 * kappa_12(s,beta) / 4 <= finite-volume physical transfer gap

1/2304 <= kappa_12(s,beta)

1/3072 <= finite-volume physical transfer gap

q0 = 3071/3072

||R_n^k x|| <= q0^k ||x||
```

uniformly in scale.

The finite top-orthogonal sectors are also embedded isometrically into one common interacting boundary product (L^2) carrier, and #4985 proves that the same (q_0^k) contraction and one-step gap floor survive any explicitly compatible common-carrier strong limit.

Therefore the active frontier is:

```text
H1:
  construct actual model-facing strong-limit compatibility data
  for the common interacting boundary carrier

THEN:
  identify/connect the limiting excitation carrier with the actual OS
  vacuum-orthogonal physical carrier without conflating top/vacuum spaces

THEN H2:
  continuum spacing-scaled dynamics / Euclidean limit

THEN H3:
  OS reconstruction and Hamiltonian

THEN H4:
  spectral / Wightman mass-gap statement
```

Do not reopen the already closed finite-volume leakage, renewal, grouping, centering or uniform-gap layers unless an actual inconsistency is found.

## 1. Closed finite-volume foundation

### A. Real leakage through all-(L^2) tagged relative Poincaré — #4935--#4971

The full chain is closed:

- real square-root leakage coefficient;
- ordered RMS Schur envelope;
- actual bounded-core terminal recurrence;
- geometric renewal and renewal-tail bridge;
- full genuine joint (L^2) propagation;
- two-boundary cross influence;
- actual two-sided leakage;
- two-sided cyclic forcing;
- strict full-sweep loss contraction;
- intrinsic constant-line fixed-space identification;
- strong convergence to the intrinsic constant projection;
- all-(L^2) two-sided tagged-link relative Poincaré.

The endpoint at #4971 is

```text
(1 - 2 Q) * ||f - B f||^2
  <= sum_e ||f - P_e f||^2,
0 < 1 - 2 Q.
```

**Status:** closed dependency.

### B. Complete-order robustness — #4976--#4978

Noncommutativity matters: the one-link conditional expectations cannot be freely reordered.

#4976 proves the strict two-boundary loss contraction for every **complete duplicate-free tagged-link order**.

#4977 constructs the fixed right-six + left-six grouped order.

#4978 extends complete-order control to:

- fixed space = intrinsic constant line;
- constant projection absorption;
- strong convergence of iterates;
- exact constant-centered Pythagoras;
- constant-centered contraction by the same two-boundary loss ratio.

**Status:** closed. Grouped order is now a theorem object, not an informal permutation.

### C. Endpoint swap and left whole-color control — #4979

#4979 lifts endpoint swap from one-link projections to:

- right/left color sigma-algebras;
- right/left color conditional expectations;
- arbitrary finite same-order right/left sweeps;
- whole-color displacement norms.

Therefore the existing right six-color displacement estimate transfers exactly to the left six-color block.

**Status:** closed.

## 2. Phase G — closed

### G1. Genuine volume-free twelve-spatial relative frame — #4980 CLOSED

Define

```text
twoSidedTwelveSpatialFrameCutoff
  = min(
      twoBoundaryOrderedLossContractionCutoff,
      jointLeakageLossContractionCutoff
    )
```

and

```text
kappa_12(s,beta)
  = (1 - sqrt(twoBoundaryOrderedLossRatio(s,beta)))^2 / 576.
```

#4980 proves on all genuine joint (L^2):

```text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f)
```

with

```text
0 < kappa_12(s,beta).
```

The coefficient is independent of:

- number of lattice links;
- finite lattice volume;
- gauge rank.

The factor (576 = 4 cdot 12^2) is fixed-cardinality only.

**Status:** CLOSED.

### G2. Intrinsic constant line -> physical top-orthogonal centered norm — #4981 CLOSED

For the full physical normalized-transfer top-eigenspace orthogonal sector and

```text
z = R (U x),
```

#4981 proves

```text
B z = 0
```

and hence

```text
||z - B z||^2 = ||x||^2.
```

This is proved from actual inner-product/isometry declarations:

- distinguished nonnegative top eigenvector lies in the full top eigenspace;
- Haar-to-vacuum transform sends it to constant one;
- genuine right-boundary lift sends that to intrinsic joint constant one;
- isometries preserve inner products.

No simplicity of the top eigenspace is assumed.

**Status:** CLOSED.

### G3. Positive-beta finite-volume physical transfer gap — #4981 CLOSED

Feeding G1 + G2 into the existing conventional twelve-spatial receiver gives

```text
3 * kappa_12(s,beta) / 4
  <= physical top-eigenspace transfer gap.
```

Therefore on the certified positive-beta interval:

```text
0 < physical finite-volume transfer gap.
```

No transfer-operator theory was rebuilt.

**Status:** CLOSED.

### G4. Explicit scale-uniform gap package — #4982 CLOSED

#4982 chooses a smaller common positive cutoff such that

```text
twoBoundaryOrderedSchurCoefficient(s,beta) < 1/3.
```

It proves

```text
1/2304 <= kappa_12(s,beta)
```

and therefore

```text
1/3072 <= physical transfer gap
```

at every scale.

The repository target

```text
PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
```

is discharged on this interval.

**Status:** CLOSED.

## 3. Post-G uniform discrete dynamics

### #4983 — uniform top-orthogonal power decay CLOSED

Set

```text
q0 = 3071/3072.
```

Then

```text
0 < q0 < 1
```

and every finite-scale top-orthogonal transfer satisfies

```text
||R_n|| <= q0
||R_n^k|| <= q0^k
||R_n^k x|| <= q0^k ||x||
```

for positive natural (k).

The associated discrete logarithmic rate is

```text
m_discrete = -log(q0) > 0.
```

This is scale/volume/rank independent.

**Status:** CLOSED.

## 4. Phase H1 — thermodynamic/common-carrier compatibility

### H1-A. Put all finite excitation sectors in one Hilbert carrier — #4984 CLOSED

The common carrier is the infinite product of the actual interacting finite boundary marginals.

For scale (n), compose:

```text
physical top-orthogonal sector
  -> shared-boundary Haar L2
  -> interacting finite boundary marginal L2
  -> common infinite-product boundary L2.
```

Every arrow is an exact linear isometry.

#4984 proves:

```text
||I_n x|| = ||x||
```

and, on each exact finite-scale image range,

```text
||T_{n,common}^k|| <= q0^k.
```

No exact restriction identity between different periodic Gibbs measures is required.

**Status:** CLOSED.

### H1-B. Preserve the gap under compatible strong limits — #4985 CLOSED

For any finite sequence (x_n) with

```text
I_n x_n -> x_limit
I_n R_n^k x_n -> y_limit
```

strongly in the common carrier, #4985 proves

```text
||y_limit|| <= q0^k ||x_limit||.
```

It also defines an explicit compatibility structure containing:

- limiting normed space (E);
- isometric `limitEmbedding : E -> common carrier`;
- finite approximants for every (x : E);
- bounded `limitOperator`;
- strong convergence of initial approximants;
- strong convergence of evolved approximants.

For any instance of this structure:

```text
||limitOperator|| <= q0^k.
```

For the one-step specialization:

```text
||T|| <= 3071/3072
1/3072 <= 1 - ||T||
||T|| < 1.
```

**Status:** abstract descent CLOSED.

### H1-C. Construct the actual model-facing strong-limit data — OPEN, immediate

This is the current frontier.

Construct an actual instance of

```text
PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryStrongLimitData
```

from the existing Wilson / OS continuum machinery.

Required objects:

1. **Limit excitation carrier**
   - choose the actual limiting Hilbert/normed carrier (E);
   - do not merely invent an abstract copy unless it connects to the OS reconstruction route.

2. **Limit embedding**
   - construct an isometric embedding
     `E -> common interacting boundary L2`.

3. **Finite approximants**
   - for every (x : E), construct
     `x_n` in the finite physical top-orthogonal sector.

4. **Initial strong convergence**
   - prove
     `I_n x_n -> I x`.

5. **Evolved strong convergence**
   - prove
     `I_n R_n x_n -> I (T x)`
     for the actual intended limit operator (T).

6. **Compatibility with the intended physical sector**
   - show that the chosen (E) is the correct excitation/vacuum-orthogonal sector for the downstream OS/Hamiltonian construction.

The repository already contains generic real-Hilbert asymptotically embedded strong-limit frameworks. Reuse them where the hypotheses match; do not duplicate them simply to rename #4985.

**Completion criterion:** a theorem-generated concrete #4985 data instance from the actual Wilson/OS scaling family.

### H1-D. Periodic OS vacuum vs one-slab top sector — OPEN, separate authority boundary

Do not silently identify:

- one-slab normalized-transfer top eigenspace;
- finite periodic OS vacuum line;
- canonical boundary vacuum;
- common-product constant line.

Existing mode-wise closure/eigenlift theorems show that realized transfer modes can be lifted into finite OS Hilbert spaces, but this does not automatically give a global equality of sectors.

Possible routes:

- prove a full boundary-closure realization theorem for the top-orthogonal sector;
- prove an exact identification theorem for the relevant finite OS vacuum/top line;
- bypass global equality by constructing H1-C approximants directly in a common carrier and only later identify the limiting vacuum-orthogonal subspace.

**Completion criterion:** the limiting contraction is known to act on the physically correct vacuum-orthogonal excitation sector.

## 5. Phase H2 — continuum Euclidean/scaling dynamics

### H2-A. Spacing-scaled rate — OPEN and conceptually essential

The fixed-step contraction

```text
q0 = 3071/3072 < 1
```

must not be naively reused as the continuum physical-time factor when lattice spacing (a_n 	o 0).

For fixed (t>0), using (lfloor t/a_nfloor) steps would give

```text
q0 ^ floor(t/a_n) -> 0.
```

This corresponds to instantaneous annihilation on the excitation sector at positive time, not a nontrivial strongly continuous (C_0) semigroup.

Therefore the continuum route needs a scaling statement of the form

```text
one-step factor_n
  = exp(-m_n a_n + o(a_n))
```

or an equivalent rescaled-generator/Dirichlet statement with a finite positive physical mass rate.

The repository already contains floor-time and derived-rate infrastructure. The next continuum bridge should feed the newly proved finite-volume coercivity into that rate-scaled machinery rather than treating (q_0) as a physical continuum-time factor.

**Status:** OPEN.

### H2-B. Euclidean limiting state / field

Continue or reuse the existing:

- tightness / weak-limit machinery;
- Euclidean covariance;
- gauge invariance;
- reflection positivity;
- compatible boundary readouts.

Quantitative gap information must survive on the actual limiting carrier.

**Status:** OPEN / partially developed elsewhere in the repository.

## 6. Phase H3 — OS reconstruction

Once H1/H2 identify the correct limiting state and scaled dynamics, connect to the existing OS reconstruction spine:

- physical Hilbert space;
- normalized vacuum;
- strongly continuous contraction semigroup;
- symmetry/self-adjointness inputs;
- closed/right Hamiltonian;
- exact vacuum-orthogonal sector.

The repository already has substantial generic OS/Hamiltonian machinery. The remaining task is to feed it theorem-generated Wilson model data without replacing missing model-facing hypotheses by names.

**Status:** downstream.

## 7. Phase H4 — spectral / Wightman mass gap

The desired final route is:

```text
uniform finite-volume coercivity
  -> correct common-carrier / scaled continuum contraction
  -> continuum OS Hamiltonian lower bound on vacuum orthogonal sector
  -> positive spectral gap
  -> Wightman / energy-momentum mass-gap statement.
```

A finite-volume gap, even a scale-uniform one, is not itself this final theorem.

**Status:** downstream.

## 8. Exact distinctions to preserve

### Beta zero vs positive beta

Beta zero remains the exact theorem

```text
gap(beta = 0) = 1.
```

The positive-beta perturbative lower bound (1/3072) is not intended to reproduce this endpoint sharply.

### Relative-frame coefficient vs uniform lower bound

#4980:

```text
kappa_12(s,beta)
  = (1 - sqrt(twoBoundaryOrderedLossRatio(s,beta)))^2 / 576.
```

#4982:

```text
1/2304 <= kappa_12(s,beta)
```

on a smaller common cutoff.

Do not replace the pointwise coefficient globally by (1/2304) outside that uniform cutoff.

### Finite gap vs discrete contraction

```text
gap_n >= 1/3072
```

is equivalent to the convenient bound

```text
||R_n|| <= 3071/3072
```

for the top-orthogonal restriction used in #4983.

The logarithmic quantity (-log(3071/3072)) is a **discrete step rate**, not automatically the continuum physical mass.

### Common carrier vs physical OS carrier

#4984's common interacting boundary (L^2) is a mathematically useful shared ambient Hilbert space. It is not by itself the final reconstructed physical Hilbert space.

#4985's limit space (E) is deliberately abstract until H1-C constructs and identifies it.

## 9. Validation and Lean engineering

### Current #4985 evidence

Exact PR head:

```text
a0db6d3d4c1184a5c81d41b4766efc12aca1e6ca
```

Run:

[36810743769](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36810743769)

Build:

```text
Build completed successfully (9678 jobs).
```

Audit:

```text
axiom: 0
forbidden Lean tokens audited:
  sorry
  admit
  axiom
  constant
```

Artifact:

```text
11139946207
sha256:ca6a88ee9772b1694a916a67651053164fab6960eb99b35da4f99b246601cf2d
```

### Lean lessons from #4984

The #4984 debugging sequence exposed two reusable Lean 4 engineering lessons.

1. **Anonymous local instance declaration-name collisions across imports**

   `local instance` limits typeclass activation, but the declaration still has a generated environment name. Importing two modules with colliding generated names can fail before theorem elaboration.

   Stable pattern: give reusable module-local instances explicit module-specific names.

2. **Dependent submodule carriers and generic `change`**

   A generic `change` can force fresh elaboration of a dependent subtype expression and trigger typeclass synthesis failure even when a suitable local instance is conceptually present.

   Stable pattern:
   - make the restricted `Submodule.normedSpace` instance explicit where needed;
   - prefer already typed named theorems;
   - use local `calc` equalities rather than broad `change` / `rw` over dependent expressions.

### Continuing workflow

For theorem PRs:

- start from fresh theorem-carrier HEAD;
- inspect the entire changed module and relevant imported modules;
- maintain source/target index orientation;
- use pinned Lean/mathlib APIs;
- separate mathematical obstruction from elaboration/import hygiene;
- validate module + CompileSmoke at the exact PR head;
- once unchanged exact head is GREEN, do not rerun expensive validation without a new reason.

For docs-only work:

- verify README/ROADMAP diff and pinned theorem SHA;
- do not present docs commits as theorem-bearing;
- do not rerun theorem validation solely because documentation changed.

## 10. Milestone ledger — #4976 through #4985

| PR | Classification | Contribution |
| --- | --- | --- |
| #4976 | Theorem | Loss contraction for arbitrary complete duplicate-free tagged-link order |
| #4977 | Theorem | Complete grouped right-six + left-six two-sided link order |
| #4978 | Theorem | Complete-order constant-line convergence and centered contraction |
| #4979 | Theorem | Whole left six-color displacement by endpoint swap |
| #4980 | Theorem | Volume-free genuine two-sided twelve-spatial relative frame |
| #4981 | Theorem | Physical top-orthogonal centering and positive finite-volume transfer gap |
| #4982 | Theorem | Uniform (1/2304) Poincaré coefficient and (1/3072) gap floor |
| #4983 | Theorem | Scale-uniform (q_0^k) top-orthogonal power decay |
| #4984 | Theorem | Exact isometric realization of all finite excitation sectors in one interacting common boundary carrier |
| #4985 | Theorem | Strong-limit preservation of (q_0^k) and one-step gap floor |

## 11. Restart sequence

Freshly re-observe:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The theorem-bearing checkpoint documented here is:

```text
88870c84503e22797397f7082a1cfc9b4dc36322
```

Classify any later HEAD as theorem-bearing, docs-only or infrastructure before using it.

Read in this order:

1. [#4985 common-carrier strong-limit preservation][strong-limit];
2. [#4984 common-carrier finite-scale realization][common-carrier];
3. [#4983 uniform power decay][power-decay];
4. [#4982 uniform gap][uniform-gap];
5. [#4981 physical centering/gap bridge][physical-gap];
6. [#4980 twelve-spatial relative frame][frame];
7. only then consult the older #4971/#4969 machinery if a dependency question arises.

Current restart target:

```text
CURRENT:
  #4985 compatible strong limits preserve the explicit q0 = 3071/3072
  contraction and the 1/3072 one-step gap floor

NEXT H1-C:
  construct the actual Wilson/OS model-facing strong-limit data instance

PARALLEL AUTHORITY BOUNDARY:
  relate the one-slab top-orthogonal sector to the actual finite/continuum
  OS vacuum-orthogonal sector without informal identification

THEN H2:
  derive spacing-scaled finite physical rate / continuum floor-time decay

THEN H3:
  feed the actual continuum data into OS semigroup + Hamiltonian reconstruction

THEN H4:
  spectral/Wightman mass-gap statement
```

Do not reopen G1--G4: they are theorem-bearing dependencies.

[frame]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialRelativeFrame.lean
[physical-gap]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialPhysicalTopOrthogonalGap.lean
[uniform-gap]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialUniformGap.lean
[power-decay]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferUniformTopOrthogonalPowerDecay.lean
[common-carrier]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryDecay.lean
[strong-limit]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88870c84503e22797397f7082a1cfc9b4dc36322/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryStrongLimit.lean
