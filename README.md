# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, finite Wilson lattice models, Osterwalder--Schrader reconstruction, transfer operators, and the mass-gap problem.

The repository keeps a strict distinction between:

1. theorems proved from the actual finite periodic Wilson model;
2. same-root continuum / OS / Hamiltonian constructions built from those finite objects;
3. reusable analytic and spectral implication machinery; and
4. model-facing or scale-uniform statements that are still open.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The canonical branch now contains a long same-root formal chain from the finite compact `SU(N)` Wilson model through finite Markov/Fubini transfer identities, OS reconstruction, completed Hilbert-space transfer operators, logarithmic-generator / spectral-floor machinery, and a fixed-ambient positive-half recursive transfer semigroup.
>
> The latest finite-transfer checkpoint proves that the canonical ambient endpoint-pair transfer is a self-adjoint contraction, all finite powers are contractions and self-adjoint, all Rayleigh quotients of those powers lie in `[-1,1]`, and the real spectrum of every finite power is contained in `[-1,1]`.
>
> What is **not** yet proved by those results is a strict spectral gap below the top spectral value, a scale-uniform vacuum-orthogonal contraction, or the full four-dimensional continuum Yang--Mills field required for a Clay-level theorem.

## Repository status — 2026-09-04 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Canonical exact SHA at this documentation checkpoint:
  e607fa92e169b47c16a240c0774bfc574a2c601e

Latest merged mathematical checkpoint represented here:
  PR #3368
  Bound pair transfer spectra by the unit interval

Public landing branch:
  main

Detailed development order:
  ROADMAP.md
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative proof status. The `main` branch is the public landing surface.

---

## Proof picture in one view

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / finite Wilson OS positivity
  -> boundary and spatial-slice Haar-L² carriers
  -> literal one-slab Wilson kernels
  -> physical one-slab transfer and finite transfer powers
  -> full positive-half Wilson path identities

B. SAME-ROOT CONTINUUM / OS LANE

finite Wilson scalar readout
  -> rational-time path law / Prokhorov continuum law
  -> continuum reflection positivity
  -> real OS Hilbert reconstruction
  -> strongly continuous contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω and complete Ω⊥ sector

C. FINITE PATH -> TRANSFER LANE

literal finite Wilson path
  -> temporal-gauge Markov/Fubini decomposition
  -> physical transfer-power matrix coefficients
  -> transfer-normalized finite-volume excitation decay
  -> boundary L² realization and one-sided boundary transfer

D. AMBIENT PAIR-HAAR LANE

literal ordered-pair one-slab kernel K_pair
  -> Hilbert-Schmidt pair transfer T_pair
  -> positive-half outer/inner/deep Haar factorization
  -> actual path amplitude = pair-transfer matrix coefficient
  -> fixed-ambient recursive messages Ψ_R
  -> Ψ_(R+2) = T_pair Ψ_R
  -> Ψ_R = T_pair^(R/2) Ψ_(R mod 2)

E. CURRENT QUANTITATIVE PAIR-TRANSFER RECEIPTS

‖T_pair‖ ≤ 1
  -> ‖T_pair^k‖ ≤ 1
  -> every T_pair^k is self-adjoint
  -> every Rayleigh quotient lies in [-1,1]
  -> spectrum_R(T_pair^k) ⊆ [-1,1]

F. NEXT GAP-RELEVANT FRONTIER

identify the physically relevant top/vacuum sector
  -> prove a strict contraction / spectral separation on its complement
  -> obtain parity-aware large-R exponential decay of Ψ_R
  -> make the estimate uniform in the scaling sequence
  -> transport it through the existing OS/Wightman machinery

G. FULL CLAY-LEVEL COMPLETION

sufficiently rich same-root 4D Yang--Mills continuum field/state   [OPEN]
full model-derived physical OS/Wightman identification              [OPEN]
strict positive spectrum above the vacuum on the full carrier       [OPEN]
Clay-level existence + mass gap                                     [OPEN]
```

---

## 1. Actual finite compact `SU(N)` Wilson root

The finite model uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized compact Haar probability structure and an interacting periodic-even Wilson Gibbs law.

Canonical finite-model infrastructure includes:

```text
oriented periodic lattice / edge / plaquette geometry
Wilson action and Gibbs probability measure
reflection geometry and positive-time decomposition
finite Wilson reflection positivity / Gram identities
gauge covariance and gauge-invariant trace observables
integer temporal translation and reflection covariance
boundary and spatial-slice Haar-L² carriers
literal temporal-gauge one-slab kernels
physical one-slab transfer operators
```

The interacting Wilson source remains visible at decisive model-facing steps; it is not silently replaced by an unrelated abstract probability model.

---

## 2. Same-root scalar continuum OS construction

The constructive continuum lane currently uses a selected primary gauge-invariant scalar Wilson process, schematically

```text
ℚ -> ℝ.
```

It is obtained from finite Wilson pushforwards. The integrated route includes:

```text
finite primary positive-half readout
reflection-completed rational-time paths
tightness / Prokhorov subsequence
continuum rational-cylinder reflection positivity
continuum reflection invariance
OS seminorm and null quotient
fixed-slot real Hilbert completions
directed-limit Hilbert carrier
real C₀ contraction semigroup
graph-closed self-adjoint Hamiltonian
vacuum Ω and complete vacuum-orthogonal sector Ω⊥
```

This is a genuine same-root continuum observable process. It is **not** yet the full continuum gauge connection or complete four-dimensional Yang--Mills local observable theory.

---

## 3. Full finite Wilson path and physical transfer are now connected

The public documentation previously stopped before the finite raw-path Markov/Fubini calculation was completed. That is no longer the current state.

The merged chain through PRs #3213--#3257 now includes:

```text
finite temporal-gauge Markov/Fubini decomposition
raw one-slab physical transfer matrix coefficients
Gauss-law projection of later kernel sections
finite Wilson recursion with a physical terminal vector
complete positive-half path integral
automatic endpoint integrability
literal full Wilson path = physical transfer-power matrix coefficient
transfer-normalized finite-volume excitation decay
raw-path decay with the exact physical top-transfer scale retained
```

Thus the old README statement that the immediate task was merely to extract one adjacent slab from the raw `H+1`-slab path is obsolete.

These are finite-volume theorems. A positive lower bound uniform in the scaling sequence remains a separate requirement.

---

## 4. Boundary `L²` and one-sided physical transfer

PRs #3260--#3277 further connect actual Wilson OS boundary moments to completed boundary Hilbert-space data.

Integrated components include:

```text
boundary moments as inserted positive-half path amplitudes
fixed-boundary unfixed path-kernel formulas
automatic shared-boundary L² membership
an automatic-analytic finite boundary-L² gap interface
one-sided physical transfer inside ordered pair-Haar L²
transport to the actual shared reflection-boundary carrier
extension from the excitation subspace to the full physical slice
```

No ambient boundary-`L²` surjectivity is inserted as a shortcut.

---

## 5. Ambient pair-Haar one-slab transfer

PR #3279 constructs the literal ordered-pair one-step kernel

```text
K_pair ((A,B),(A',B')) = K(A,A') * K(B,B')
```

on the pair-Haar carrier and its Hilbert-Schmidt transfer operator `T_pair`.

The subsequent finite Markov/Fubini chain (#3291--#3322) proves, in the nondegenerate positive-half geometry, that the actual Wilson path can be split into outer pair, inner pair, and deeper interior coordinates, and that the resulting positive-half amplitude is exactly a pair-transfer matrix coefficient.

The `H = 1` central-slice geometry remains separate. It is a diagonal central configuration and is **not** replaced by two falsely independent pair-Haar variables.

---

## 6. Fixed-ambient recursive transfer semigroup

A key type-theoretic issue is now resolved canonically.

A recursion that decrements a parameter tied to the ambient spatial size would change the Hilbert carrier and is therefore not a legitimate single-operator recursion. The canonical construction instead keeps ambient spatial extent `H` fixed and decreases only the remaining inward chain length `R`.

The terminal geometries are exactly:

```text
R = 0 : literal central one-slab terminal
R = 1 : diagonal central pair terminal (C,C)
R+2   : peel one inward endpoint pair and recurse at the same ambient H
```

After measurability, Fubini, and `L²` lifting, the repository proves

```text
Ψ_(R+2) = T_pair Ψ_R
```

on one fixed pair-Haar `L²` carrier, and then the parity formulas

```text
Ψ_(2m)   = T_pair^m Ψ_0
Ψ_(2m+1) = T_pair^m Ψ_1
```

as well as the parity-uniform normal form

```text
Ψ_R = T_pair^(R / 2) Ψ_(R % 2).
```

Representative merged milestones are PRs #3327--#3352.

---

## 7. Quantitative and spectral pair-transfer checkpoint

The most recent merged sequence adds a clean operator-theoretic layer on the same ambient pair-Haar carrier:

```text
PR #3354  ‖T_pair‖ ≤ 1
PR #3358  recursive-message norm contraction
PR #3361  ‖T_pair^k‖ ≤ 1 and vector contraction for every k
PR #3364  T_pair and every finite power are self-adjoint
PR #3366  all finite-power Rayleigh quotients lie in [-1,1]
PR #3368  spectrum ℝ (T_pair^k) ⊆ [-1,1] for every finite k
```

The final statement currently formalized is therefore

```text
spectrum ℝ (T_pair ^ k) ⊆ Set.Icc (-1 : ℝ) 1
```

for every finite `k`, together with the one-step specialization.

This is a contraction/spectral-location theorem, **not** yet a strict mass-gap theorem. In particular, `[-1,1]` should not be silently tightened to `[0,1]` without a separate positivity theorem for this exact operator, and no strict separation from the top spectral value is presently being claimed here.

---

## 8. Existing transfer / Wightman and exact-mode machinery

The repository also contains substantial downstream implication machinery:

```text
completed physical transfer spectral calculus
partial logarithmic transfer generator
intrinsic spectral-floor machinery
canonical transfer spectral operator core
common-core Hilbert equivalence and self-adjoint closure transfer
transfer-energy <-> Wightman-Hamiltonian point-energy implications
SU(2) selected exact-mode common-carrier chain
```

These theorems make the dependency graph precise. They do not turn a finite contraction estimate into a full physical mass gap unless the required same-root model and scale-uniform inputs are actually supplied.

Important permanent distinctions are:

```text
one positive Hamiltonian eigenmode != global spectral gap
finite-volume positive decay rate != scale-uniform continuum gap
selected scalar continuum process != full 4D Yang--Mills field
symbolic exactGapValueReal != a numerical literal without an explicit Lean theorem
```

---

## 9. Immediate frontier after PR #3368

The finite-transfer problem is now positioned at a more genuinely spectral stage.

The next useful proof targets are:

1. identify the physically relevant top/vacuum sector for the ambient pair-transfer operator;
2. derive any stronger positivity/nonnegative-spectrum statement only from the actual kernel/model structure, rather than assume it;
3. prove a **strict** contraction or spectral separation on the appropriate vacuum-orthogonal / excitation sector;
4. convert that separation into explicit parity-aware large-`R` exponential decay for the fixed-ambient recursive messages;
5. prove the needed lower bound uniformly along the scaling sequence; and
6. transport the resulting finite spectral control through the existing same-root OS/Wightman machinery.

This is also where the older scale-uniform Poincaré/coercive lane remains relevant: it can provide a global lower-bound route if the required model-derived uniform estimate is established.

---

## 10. What remains open for a Clay-level theorem

A Clay-level completion still requires a sufficiently rich four-dimensional continuum Yang--Mills theory on one coherent physical carrier, with the required combination of

```text
Euclidean covariance
gauge-invariant local observable content / gauge structure
reflection positivity
regularity / distributional control
physical nontriviality
vacuum structure and clustering
OS/Wightman reconstruction from the same model
and a strictly positive spectral gap above the vacuum
```

The repository should therefore be read as a formalized constructive program with substantial proved theorem chains and increasingly sharp open interfaces, not as a completed Millennium-prize proof.

---

## 11. Dobrushin lane: correct diagnostic, not the active continuum mechanism

The finite high-temperature covariance lane remains valid, with the active majorant

```text
q(β) = (exp(4β)-1)/(exp(4β)+1).
```

Because `q(β) -> 1` and the associated geometric factor `18 q(β) -> 18` as `β -> +∞`, that particular Dobrushin mechanism cannot supply the desired scale-independent `< 1` contraction in the large-`β` scaling regime. It remains a useful finite-volume theorem and obstruction diagnostic.

---

## 12. Key files near the current finite-transfer frontier

```text
MGAP4D/MathlibAnalytic/

  # ambient pair transfer
  PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2Transfer.lean
  PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferSelfAdjoint.lean
  PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferRayleighContraction.lean
  PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferSpectrumContraction.lean

  # fixed-ambient recursion
  PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeel.lean
  PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel.lean
  PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage.lean
  PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveMeasurability.lean
  PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveOperator.lean
  PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveIteration.lean
```

See `ROADMAP.md` for the ordered milestone chain and next completion criteria.

---

## Validation and repository discipline

The authoritative workflow is conservative by design:

```text
start theorem work from the exact canonical SHA
accept CI only when workflow / job / exact Lean step are terminal success
never count queued or in_progress as validation
inspect a terminal failure before repairing it
keep changes additive / tighten-only unless correcting an error
forbid sorry / admit / axiom / placeholder constant escapes
fresh-check base/head/mergeability/reviews/threads before merge
normal-merge with expected head SHA pinned
verify merge-parent order and the resulting canonical exact SHA
```

This discipline is part of the mathematical claim boundary, not merely repository housekeeping.
