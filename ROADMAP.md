# MGAP4D ROADMAP

## Authority checkpoint — 2026-10-01 JST

| Item | Value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique authoritative theorem-carrier | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing snapshot | `22bfe27324e374242aad7bc402a224769306a22b` |
| Latest theorem merge | [PR #4971](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4971), all-(L^2) two-sided relative Poincaré |
| #4971 validated PR head | `cf43f174d76451400bb10301c6cb2549be0118b6` |
| #4971 validation | [PR Lean Fast Check 36784485909](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36784485909): completed / success; matching exact-head receipt: success |
| Build | `Build completed successfully (9420 jobs)` |
| Artifact | `11129237482`; `sha256:2601e587a80eeb3692f12db43fdcd90a3f1e88b465922f18a2efa4569bddde6c` |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Overview](README.md)

The default branch `main` is not theorem authority. Documentation mirrors on `main` must point back to an exact theorem-carrier snapshot and must never be treated as a second theorem source. A docs-only merge may move a branch pointer without adding theorem content.

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / memory.

## 0. Current frontier

The immediate finite-volume frontier is **no longer leakage, renewal, or two-sided sweep convergence**. Those layers have been closed.

At #4971, for the genuine two-sided one-link conditional expectations `P_e`, the intrinsic constant-line projection `B`, and

```text
Q = twoBoundaryOrderedSchurCoefficient(s,beta),
```

the theorem-carrier proves on the same volume/rank-independent #4969 cutoff:

```text
0 < 1 - 2 Q

(1 - 2 Q) * ||f - B f||^2
  <= sum_e ||f - P_e f||^2
```

for **every genuine joint (L^2) vector**.

This is the current mathematical endpoint.

The next problem is to turn this tagged-link relative Poincaré theorem into the fixed-cardinality two-sided spatial frame expected by the already-existing physical transfer-gap receivers, without introducing lattice-volume loss and without silently identifying the intrinsic constant line with the physical vacuum-orthogonal sector.

## 1. Retained completed foundation

The following layers should not be reopened unless a genuine inconsistency is found.

### A. Exact source-fixed / leakage chain — through #4934

Retained from the previous checkpoint:

- exact cyclic carrier and between-visits trajectory;
- bounded representatives for actual intermediate sweep states;
- exact stage residual and original/terminal profile classification;
- signed source-fixed Hilbert pairing;
- source-residual forcing receiver;
- source-invariant representative of the actual source update;
- canonical mean = genuine `CondExpL2`;
- exact conditional iid factor-two normalization;
- exact stationary source variance;
- genuine joint double-projection leakage numerator.

These are dependencies, not the active frontier.

### B. Real coefficient and ordered Schur closure — #4935--#4937

#4935 converts the genuine squared leakage estimate to an exact real norm coefficient and reuses the existing bounded-core forcing receiver.

#4936 constructs the ordered RMS Schur envelope and a uniform small-coupling cutoff.

#4937 closes the actual bounded-core terminal recurrence with the ordered envelope.

**Status:** closed.

### C. Renewal and all-(L^2) propagation — #4938--#4941

#4938 derives fixed-color geometric loss decay and the explicit renewal-tail bridge.

#4939 identifies the actual fixed-color sweep limit and closes uniform renewal-defect contraction.

#4940 moves the ordered defect estimate to the full genuine joint (L^2) carrier.

#4941 controls arbitrary all-link mixed-color sweep residuals by the exact ordered Schur energy.

**Status:** closed. The earlier “strict renewal contraction” item is no longer an external hypothesis in this route.

### D. One-sided volume-free grouping — #4942--#4945

#4942 proves an all-right relative Poincaré theorem with the complete retained left boundary.

#4943 groups the right-link family into the six canonical spatial colors and proves

```text
((1 - 2 Q_right)^2 / 36) * ||f - C_left f||^2 <= E_6(f),
```

using Cauchy--Schwarz only over `Fin 6`. No lattice-volume factor appears.

#4944 supplies the retained-boundary physical-gap receiver: if the retained-left projection contracts the physical top-orthogonal sector by some `rho < 1`, then the six-color relative frame yields a positive physical transfer gap.

#4945 identifies the retained projection with the coarse / Doob geometry.

**Status:** one-sided frame closed; the old receiver remains valid but its retained-contraction premise is not used as an unproved shortcut in the new two-sided route.

### E. Two-sided cross-boundary kernel — #4946--#4966

This block supplies the missing genuine left/right coupling:

- #4946 two-boundary ordered Schur envelope;
- #4947 genuine left and two-sided one-link projections;
- #4948 variance-sensitive (L^2) mean difference under mutual Harnack domination;
- #4949 specialization to cross-boundary fiber laws;
- #4950 endpoint swap symmetry;
- #4951 conjugation of genuine one-link projections by swap;
- #4952 exact cancellation of the independent-pair factor two;
- #4953 reference fiber = updated kernel-section fiber;
- #4954 actual kernel-section cross-boundary (L^2) estimate;
- #4955 concrete source-invariant target means;
- #4956 source-fiber integrated target response;
- #4957 source profile = current target section;
- #4958 target variance = current source section;
- #4959 exact one-link stationarity return;
- #4960 genuine joint-swap transport;
- #4961 target variance = genuine target residual;
- #4962 source variance = genuine left leakage;
- #4963 genuine cross-boundary one-step (L^2) influence;
- #4964 actual left one-link update estimate;
- #4965 exact diagonal-support preservation;
- #4966 actual two-sided one-link leakage with the ordered block kernel.

**Status:** closed.

### F. Two-sided recurrence, contraction and relative Poincaré — #4967--#4971

#4967 builds the bounded-core two-sided cyclic forcing budget.

#4968 closes the actual two-sided ordered terminal recurrence.

#4969 introduces the volume/rank-independent loss-contraction cutoff and

```text
eta = (Q / (1 - Q))^2,   0 <= eta < 1,
```

then proves on all genuine joint (L^2)

```text
loss(S f) <= eta * loss(f)
```

and geometric path-loss decay.

#4970 identifies the full two-sided sweep fixed space with the intrinsic joint constant line, constructs its orthogonal projection `B`, proves absorption, and establishes strong convergence

```text
S^[n] f -> B f.
```

#4971 combines exact Pythagoras, #4969 loss decay, #4970 convergence and the all-(L^2) cross-step estimate to prove

```text
(1 - 2 Q) * ||f - B f||^2
  <= sum_e ||f - P_e f||^2.
```

The coefficient `1 - 2 Q` is strictly positive on the same cutoff.

**Status:** closed. This is the authoritative current theorem endpoint.

## 2. Current theorem units — Phase G

### G1. Volume-free grouped two-sided spatial frame — OPEN, immediate

The #4971 right-hand side is

```text
sum over every tagged two-sided spatial link e of ||f - P_e f||^2.
```

It is **not** the conventional normalized twelve-spatial residual, and replacing one by the other with a factor equal to the number of links would destroy volume uniformity.

Construct a grouping theorem analogous to #4943:

1. partition the tagged two-sided links into the fixed twelve canonical spatial colors (six right + six left);
2. define / reuse the corresponding block conditional expectations or full same-color sweeps;
3. compare full block displacement with block residuals using the already-proved two-sided loss contraction;
4. perform Cauchy--Schwarz only over the fixed color type, not over all links;
5. obtain a coefficient independent of `H` and lattice link count.

Preferred target: a theorem on all genuine joint (L^2) of the shape

```text
kappa_12(s,beta) * ||f - B f||^2
  <= E_12(f),
0 < kappa_12(s,beta),
```

where `E_12` is either the conventional `1/12` twelve-spatial residual or the already-existing physical `1/8`-normalized two-sided twelve-spatial energy.

**Completion criterion:** no cardinality factor depending on lattice volume; coefficient positivity follows from the same certified #4969 cutoff.

### G2. Constant-line projection on physical right-boundary top-orthogonal vectors — OPEN

The grouped theorem remains centered at

```text
B = intrinsic joint constant-line orthogonal projection.
```

The physical receiver is stated on right-boundary lifts of the transfer top-eigenspace orthogonal sector.

Prove the exact relation needed for

```text
z = R (U x),
```

with `x` in the physical top-orthogonal carrier. The ideal endpoint is

```text
B z = 0
```

or equivalently

```text
||z - B z||^2 = ||x||^2
```

after the existing isometries. If the precise carrier geometry gives a different but sufficient identity, prove that explicitly.

Do not identify “constant line”, “vacuum line”, “retained boundary”, and “top eigenspace” by name alone. Use the actual inner-product / projection declarations.

**Completion criterion:** a formal centered-norm bridge on the exact physical sector required downstream.

### G3. Positive-beta finite-volume physical transfer gap — OPEN

Two receiver lanes already exist.

#### Conventional 12-spatial receiver

`PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap.lean` proves:

```text
uniform positive 1/12 twelve-spatial Poincare on physical right lifts
  -> six-spatial physical frame
  -> transfer gap,
```

with explicit finite-volume lower bound

```text
3 * kappa / 4 <= physical transfer gap.
```

#### Physical 1/8-normalized two-sided frame receiver

`PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialFrame.lean` proves that on right-boundary lifts the two-sided (1/8)-normalized residual reduces exactly to the existing physical eight-color residual and feeds the raw physical squared defect.

Choose the lane that gives the cleanest coefficient from G1--G2. Do not rebuild the transfer-operator layer.

**Completion criterion:** a theorem with no extra model-facing hypothesis beyond the already-certified high-temperature cutoff, proving

```text
0 < physical finite-volume transfer gap
```

for positive beta in a nonempty interval.

### G4. Scale-uniform packaging — OPEN immediately after G3

The #4969 cutoff is already volume/rank-independent for fixed `s > 8`, and #4971 positivity is on that same cutoff.

After G1--G3, package a single `kappa > 0` for a scaling family and invoke the existing uniform transfer-gap infrastructure.

Check explicitly that:

- no G1 coefficient depends on the number of links;
- no G2 constant depends on volume;
- the same beta interval works for every scale;
- all sector and normalization hypotheses match the existing uniform receiver.

**Completion criterion:** a formally checked uniform positive finite-volume physical transfer gap along the intended scaling family.

## 3. Downstream Phase H — thermodynamic and continuum mass-gap construction

Only after Phase G is closed should the main frontier move downstream.

### H1. Thermodynamic compatibility

Construct / verify compatible finite-volume embeddings, restrictions and vacuum states. Prove the uniform gap estimate is stable under the chosen limiting carrier.

### H2. Euclidean continuum control

Build the continuum Euclidean field/state with the required tightness, covariance and reflection-positive structure. Preserve the quantitative gap input through the scaling / continuum passage.

### H3. OS reconstruction

Verify the continuum Osterwalder--Schrader axioms on the actual limiting object and reconstruct:

- physical Hilbert space;
- vacuum;
- strongly continuous Euclidean-time / physical-time semigroup;
- self-adjoint Hamiltonian;
- correct vacuum-orthogonal sector.

### H4. Spectral / Wightman mass gap

Transport the surviving positive spectral gap to the reconstructed Hamiltonian and then to the desired Wightman / energy-momentum mass-gap statement.

A finite-volume gap, even a uniform one, is not itself the complete continuum theorem.

## 4. Exact endpoint distinctions to preserve

### Beta zero

The repository already proves the exact endpoint

```text
physical transfer gap at beta = 0 = 1.
```

Do not replace this by the weaker perturbative constants arising from the positive-beta route.

### One-sided vs two-sided coefficients

The #4943 one-sided six-color theorem has coefficient

```text
(1 - 2 Q_right)^2 / 36.
```

The #4971 two-sided tagged-link theorem has coefficient

```text
1 - 2 Q_two-sided.
```

They control different energies and centers. Do not compare these coefficients without translating the right-hand-side normalization.

### Tagged links vs color blocks

#4971 sums residuals over all tagged links. The physical receivers use fixed-color block energies. A volume-free grouping theorem is a real proof obligation, not a formatting conversion.

### Constant line vs retained boundary

#4970's intrinsic constant line is the intersection of **all two-sided tagged-link fixed spaces**. The older #4942--#4945 one-sided route centers on a retained boundary projection. These are distinct structures even when later theorems relate them.

## 5. Validation and Lean engineering

### #4971 evidence

Exact PR head:
`cf43f174d76451400bb10301c6cb2549be0118b6`

Run:
[36784485909](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36784485909)

Build:
```text
Build completed successfully (9420 jobs).
```

Artifact:
```text
11129237482
sha256:2601e587a80eeb3692f12db43fdcd90a3f1e88b465922f18a2efa4569bddde6c
```

The new #4971 theorem and CompileSmoke build successfully. Its reported axioms are the normal classical / quotient dependencies plus the repository's existing native-decide cardinal certificates; no `sorryAx` is present.

### Lean continuation rules

For theorem PRs:

- start from a fresh theorem-carrier HEAD;
- inspect the entire changed module, not only the CI line;
- check imports and local instances explicitly;
- prefer pinned mathlib APIs over guessed theorem names;
- avoid broad dependent `rw` when a focused `change`, `simpa only`, `congrArg`, or explicit application is more stable;
- retain exact index orientation in all source/target kernels;
- keep density/closedness extensions separated from bounded-core proofs;
- validate theorem module and CompileSmoke at the exact PR head;
- once the exact unchanged head is GREEN, do not rerun Strict Lean without a new reason.

For README / ROADMAP-only work, inspect only the documentation diff and link/SHA correctness. Do not run expensive theorem validation for an unchanged theorem snapshot.

## 6. Milestone ledger since the #4932 docs checkpoint

| PR | Classification | Contribution |
| --- | --- | --- |
| #4935 | Theorem | Exact real joint-leakage norm bridge |
| #4936 | Theorem | Ordered RMS Schur envelope and uniform cutoff |
| #4937 | Theorem | Actual bounded-core terminal recurrence |
| #4938 | Theorem | Geometric fixed-color loss and renewal-tail bridge |
| #4939 | Theorem | Fixed-color sweep limit and renewal contraction |
| #4940 | Theorem | Full-joint-(L^2) ordered defect control |
| #4941 | Theorem | All-link full-(L^2) sweep residual control |
| #4942 | Theorem | All-right relative Poincaré |
| #4943 | Theorem | Volume-free ordered six-color relative frame |
| #4944 | Theorem | Retained-boundary physical-gap receiver |
| #4945 | Theorem | Retained projection = coarse / Doob geometry |
| #4946 | Theorem | Two-boundary ordered Schur envelope |
| #4947 | Theorem | Genuine left and two-sided one-link projections |
| #4948--#4954 | Theorems | Harnack (L^2), swap symmetry, factor-two cancellation and actual cross-boundary fibers |
| #4955--#4962 | Theorems | Cross-boundary means / variance / stationarity and genuine left leakage |
| #4963--#4966 | Theorems | Genuine cross-boundary one-step estimate through actual two-sided leakage |
| #4967 | Theorem | Two-sided cyclic forcing budget |
| #4968 | Theorem | Actual two-sided ordered terminal recurrence |
| #4969 | Theorem | Strict all-(L^2) full-sweep loss contraction |
| #4970 | Theorem | Intrinsic constant-line convergence |
| #4971 | Theorem | All-(L^2) two-sided relative Poincaré |

## 7. Restart sequence

Freshly re-observe `formal/real-hilbert-uniform-coercive-strong-limit`. The theorem-bearing checkpoint documented here is

```text
22bfe27324e374242aad7bc402a224769306a22b
```

and any later commit must first be classified as theorem-bearing, docs-only, or infrastructure.

Read in this order:

1. [#4971 two-sided relative Poincaré][two-sided-poincare];
2. [#4970 constant-line convergence][constant-line];
3. [#4969 loss contraction][two-sided-loss];
4. [#4943 one-sided volume-free grouping][six-color];
5. [existing twelve-spatial gap receiver][twelve-gap];
6. [existing physical (1/8)-normalized two-sided frame receiver][twelve-frame].

Then implement G1, not another leakage theorem.

```text
CURRENT:
  all-L2 two-sided tagged-link relative Poincare around intrinsic constants

NEXT G1:
  volume-free grouping -> genuine two-sided 12-spatial frame

NEXT G2:
  intrinsic constant projection -> physical top-orthogonal centered norm

THEN G3:
  existing 12-spatial / 1/8 physical receiver -> positive-beta transfer gap

THEN G4:
  uniform scaling-family packaging

LATER:
  thermodynamic + continuum OS/Wightman mass-gap construction
```

Do not reopen the real square-root conversion, terminal recurrence, strict renewal contraction, cross-boundary target/source variance bridge, two-sided loss contraction, or constant-line convergence: these are already theorem-bearing dependencies.

[two-sided-loss]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedLossContraction.lean
[constant-line]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedConstantLineConvergence.lean
[two-sided-poincare]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedRelativePoincare.lean
[six-color]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOrderedRelativeFrame.lean
[twelve-gap]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap.lean
[twelve-frame]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialFrame.lean
