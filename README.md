# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Osterwalder--Schrader reconstruction, transfer operators, and the mass-gap problem.

The repository is intentionally strict about claim boundaries. It separates:

1. theorems proved from the actual finite periodic Wilson model;
2. same-root continuum / OS / Hamiltonian constructions built from those finite objects;
3. finite-volume transfer, spectral, resolvent, Green-operator, and Poincaré theorems;
4. implication machinery that becomes physically decisive only after its model-facing hypotheses are discharged; and
5. the still-open steps required for a full four-dimensional Yang--Mills existence-and-mass-gap theorem.

> **Current claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The canonical theorem carrier now contains a strong finite-volume physical-pair theory: completed orthogonal decomposition, strict non-top contraction, power decay, strong convergence to the full completed top-top projection, fixed-space characterization, coercivity, real spectral exclusion, quantitative real resolvent bounds, a non-top Green operator, exact reduced-range identification, and a finite-volume relative Poincaré estimate.
>
> These are genuine finite-volume results. They do **not** yet provide a scale-uniform lower bound, thermodynamic/continuum propagation, top-sector simplicity, vacuum uniqueness, or a completed full four-dimensional continuum Yang--Mills field.

## Repository status — 2026-09-06 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Mathematical checkpoint documented here:
  0d947530acc81c4d0fe05aeada6dba390d6cda78

Latest merged mathematical checkpoint:
  PR #3507
  Add finite-volume physical pair relative Poincare estimate

Public landing branch:
  main

Detailed development order:
  ROADMAP.md
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative proof status.

---

## Proof picture in one view

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> physical spatial-slice and boundary L² carriers
  -> normalized one-slab physical transfer
  -> completed physical pair carrier

B. SAME-ROOT SCALAR CONTINUUM OS LANE

finite Wilson scalar readout
  -> rational-time path law
  -> same-root continuum scalar law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C₀ contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω and complete Ω⊥ sector

C. FINITE PHYSICAL-PAIR LANE

one-slice top eigenspace F and K = Fᗮ
  -> completed top-top block TT
  -> completed non-top block NN
  -> physical pair carrier PP = TT ⊕ NN
  -> strict non-top contraction q = ‖R‖ < 1
  -> q^k decay on NN
  -> S₂^k x -> P_TT x for x ∈ PP
  -> Fix(S₂ | PP) = TT
  -> coercivity / real-spectrum / resolvent control on NN
  -> Green operator for I - SN
  -> range(I - S₂ | PP) = NN = PP ⊓ TTᗮ
  -> relative finite-volume Poincaré estimate

D. SU(2) EXACT-MODE LANE

selected physical mode + normalized top companion
  -> raw one-slab Wilson kernel coefficient
  -> realizable one-step raw-kernel limit/coherence condition        [OPEN MODEL INPUT]
  -> selected completed-boundary weak identity                       [generated downstream]
  -> finite/common-carrier exact mode                                [implication machinery]
  -> graph-closed Ω⊥ Hamiltonian mode at exactGapValueReal            [implication machinery]

E. GLOBAL MASS-GAP FRONTIER

finite-volume q(H,N,β) < 1
  -> scale-uniform positive residual factor                          [OPEN]
  -> stable finite-volume Poincaré / Green control                   [OPEN]
  -> thermodynamic/scaling-limit transfer                            [OPEN]
  -> full same-root physical continuum carrier                       [OPEN]
  -> positive spectrum above the vacuum                              [OPEN]
  -> Clay-level existence + mass gap                                 [OPEN]
```

The important update is that the earlier “prove a finite pair-sector coercive/Poincaré estimate” goal is now complete at each fixed finite volume. The next global problem is no longer the existence of a finite-volume inequality; it is whether the contraction/residual factor can be controlled **uniformly along the physically relevant scaling family**, and then transported without losing the same-root physical interpretation.

---

## 1. Actual finite compact `SU(N)` Wilson root

The finite model uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar probability structure and an interacting periodic-even Wilson Gibbs law.

Canonical finite-model infrastructure includes:

```text
oriented periodic lattice / edge / plaquette geometry
Wilson action and Gibbs probability measure
reflection geometry and positive-time decomposition
finite Wilson reflection positivity / Gram identities
gauge covariance of plaquette holonomy
gauge invariance of normalized trace observables
integer temporal translation and reflection covariance
physical spatial-slice Haar-L² carriers
boundary Haar-L² carriers
normalized one-slab transfer operators
completed pair-Hilbert transfer machinery
```

The interacting Wilson measure is not silently replaced by Haar measure at nonzero coupling.

---

## 2. Same-root scalar continuum OS construction

The repository contains a constructive scalar continuum OS lane obtained from actual finite Wilson pushforwards.

Integrated structure includes:

```text
primary gauge-invariant scalar Wilson readout
reflection-completed rational-time paths
tightness / Prokhorov subsequential continuum law
continuum rational-cylinder reflection positivity
continuum reflection invariance
OS seminorm and null quotient
fixed-slot real Hilbert completions
directed-limit Hilbert carrier
real strongly continuous contraction semigroup
right generator and graph closure
self-adjoint graph-closed OS Hamiltonian
normalized vacuum Ω
complete vacuum-orthogonal sector Ω⊥
```

This is a genuine same-root continuum observable process. It is **not** yet the complete four-dimensional continuum gauge field on `ℝ⁴`.

---

## 3. Transfer / logarithmic-generator / Wightman machinery

The canonical branch also contains substantial analytic machinery around positive transfer operators and their logarithmic generators:

```text
compact positive transfer spectral support
strictly-positive spectral support lane
partially-defined logarithmic generator
resolvent and effective-energy identities
intrinsic logarithmic spectral floor
spectral-mode operator core
common-core / self-adjoint intertwining machinery
transfer point energies <-> target Hamiltonian point energies
mass-gap certificate implication machinery
```

These results make the logical bridge precise. They do not replace the remaining model-facing realization work.

---

## 4. Current finite-volume physical-pair theorem bundle

At fixed finite-volume data `(H,N,β)`, let schematically:

```text
F   = full eigenvalue-one subspace of the normalized one-slice physical transfer
K   = Fᗮ
PP  = completed physical pair carrier
TT  = completed F ⊠ F top-top block
NN  = completed non-top block inside PP
R   = one-slice orthogonal transfer restriction
q   = ‖R‖
S₂  = normalized physical pair transfer on the ambient pair carrier
SN  = completed restriction of S₂ to NN
```

The canonical branch now proves, without assuming that `F` or `TT` is one-dimensional:

### Completed pair geometry

```text
TT ⟂ NN
PP decomposes into the completed top-top and non-top sectors
NN = PP ⊓ TTᗮ
```

The relative intersection with `PP` is essential. No ambient full-pair-Haar identity `NN = TTᗮ` is claimed.

### Strict finite-volume contraction

```text
q = ‖R‖ < 1
‖SN‖ ≤ q
‖SN^k x‖ ≤ q^k ‖x‖
```

### Asymptotic top projection

For `x ∈ PP`, the pair transfer converges strongly to the projection onto the **full** completed top-top block:

```text
‖S₂^k x - P_TT x‖ ≤ q^k ‖P_(TTᗮ) x‖
S₂^k x -> P_TT x
```

and

```text
S₂ x = x  <->  x ∈ TT       (for x ∈ PP).
```

This is a fixed-space theorem for the full top sector, not a vacuum-uniqueness theorem.

### Non-top coercivity

```text
0 < 1 - q
(1 - q) ‖x‖ ≤ ‖x - SN x‖      for x ∈ NN.
```

Hence `I - SN` has trivial kernel.

### Real point spectrum and real spectrum

The non-top real point spectrum is confined to the contraction disk, and the full real spectrum satisfies

```text
spectrum ℝ SN ⊆ [-q, q] ⊂ (-1,1).
```

For real `λ` with `q < |λ|`, `λ` lies in the real resolvent set.

### Quantitative real resolvent

For `q < |λ|`, the canonical theorem gives

```text
‖resolvent SN λ‖ ≤ (|λ| - q)⁻¹.
```

This is finite-volume and real-resolvent control; no complex-spectrum or scale-uniform resolvent theorem is claimed.

### Non-top Green operator

At `λ = 1`, define the finite-volume Green operator schematically by

```text
G = (I - SN)⁻¹.
```

The canonical branch proves two-sided inverse identities and

```text
‖G y‖ ≤ (1 - q)⁻¹ ‖y‖
‖G‖ ≤ (1 - q)⁻¹,
```

with existence and uniqueness for the completed non-top Poisson equation.

### Reduced range

The physical-pair residual has exactly the completed non-top range:

```text
range(I - S₂ | PP) = NN = PP ⊓ TTᗮ.
```

Every non-top residual has a unique reduced preimage in `NN`, with the Green bound above.

### Relative Poincaré estimate — PR #3507

For every `x ∈ PP`, the canonical branch now proves

```text
(1 - q) ‖P_(TTᗮ) x‖ ≤ ‖x - S₂ x‖,
```

and equivalently

```text
‖P_(TTᗮ) x‖ ≤ (1 - q)⁻¹ ‖x - S₂ x‖.
```

This is the current finite-volume Poincaré endpoint. It controls distance to the **full completed top-top block**, not distance to a selected vacuum line.

---

## 5. Recent finite-pair milestones

The current finite-volume line was built as one mathematical unit across small CI/review PRs. Representative merged milestones are:

```text
#3436  Prove pair top-eigenspace block orthogonality
#3438  Lift pair block orthogonality to generated spans
#3440  Complete pair block orthogonality under Hilbert closure
#3442  Expose physical top-eigenspace orthogonal decomposition
#3445  Decompose the physical pair carrier into four transfer blocks
#3448  Complete the physical pair carrier orthogonal decomposition
#3457  Establish three-block contraction bounds
#3470  Complete finite-volume non-top contraction
#3474  Add finite-volume non-top power decay
#3477  Prove asymptotic convergence to the full top projection
#3480  Characterize the finite-volume fixed space
#3482  Derive non-top transfer coercivity
#3485  Exclude non-top real point spectrum outside the contraction disk
#3487  Bound the real spectrum by the contraction factor
#3495  Add the quantitative real resolvent bound
#3501  Add the finite-volume non-top Green operator
#3503  Characterize the reduced transfer range
#3507  Add the finite-volume relative Poincaré estimate
```

The mathematical point is the completed chain, not the PR granularity.

---

## 6. SU(2) exact-mode lane: current model-facing seam

The exact-mode lane has also advanced beyond the older PR #3151 checkpoint.

By PR #3177, the selected completed-boundary weak hypothesis was pushed upstream to a finite-model statement involving:

```text
selected physical/top endpoint pair
literal normalized one-slab raw Wilson kernel coefficient
projected synthesis density
realizable integer one-step raw-kernel limit
explicit finite/common-time coherence
```

The downstream selected weak identity, exact common-carrier mode, and graph-closed Hamiltonian mode are theorem-generated once those finite raw-model inputs are supplied.

What remains open is therefore not an arbitrary postulated eigen-equation. It is the **raw-model one-step limit/coherence theorem** needed to generate the selected weak identity from the literal Wilson model.

This exact-mode lane and the global finite-volume Poincaré lane solve different problems:

```text
exact-mode lane:
  construct a selected positive-energy mode

global Poincaré lane:
  control all directions orthogonal to the full top sector
```

Neither automatically implies the other.

---

## 7. Immediate frontier: from finite-volume `q < 1` to a uniform gap mechanism

The most important new global question is whether the finite-volume factor

```text
1 - q(H,N,β)
```

admits a positive lower bound along the physically relevant approximating/scaling family.

The current canonical theorems give excellent consequences **if** such control is available, but they do not manufacture it.

The next proof program should therefore distinguish two possibilities:

```text
A. prove a model-derived scale-uniform bound
   inf_n (1 - q_n) > 0

or

B. prove that this particular norm factor degenerates in the desired scaling regime,
   then replace it by a stronger model-derived coercive quantity that remains uniform.
```

No new unproved “uniform hypothesis” should be introduced merely to move the chain forward.

Once a genuinely model-derived uniform estimate exists, the finite-volume Green/Poincaré machinery is already positioned to propagate it into stable residual control and then into the continuum/OS spectral lane.

---

## 8. Top sector is deliberately not collapsed to a vacuum line

The current theorems use the full completed top-top block `TT`.

They do **not** prove:

```text
dim TT = 1
top eigenspace simplicity
vacuum uniqueness
TT = span{Ω}
```

Therefore the finite-volume Poincaré estimate is a **relative-top-sector** statement. Any later theorem that turns it into a vacuum-orthogonal mass-gap inequality must separately prove the required top-sector identification or use a formulation that does not require one-dimensionality.

This distinction is mathematically essential.

---

## 9. Dobrushin high-temperature lane remains diagnostic

The repository retains the finite-volume Dobrushin covariance lane with active single-link majorant

```text
q_D(β) = (exp(4β)-1)/(exp(4β)+1).
```

Its high-β asymptotics show that the associated simple geometric contraction mechanism cannot supply a scale-independent `< 1` factor when `β -> +∞` in the relevant regime.

That result remains useful as an obstruction/diagnostic. It is not the current physical continuum mass-gap mechanism.

---

## 10. What is still open before a Clay-level theorem

A full theorem still requires, on one coherent same-root physical construction:

```text
a sufficiently rich four-dimensional continuum Yang--Mills field/state
Euclidean covariance and gauge-invariant local observable structure
reflection positivity and regularity/distributional control
physical nontriviality
vacuum structure
OS/Wightman identification on the actual physical carrier
a strictly positive spectral gap above the vacuum
```

The current scalar continuum process, transfer spectral machinery, exact selected mode, and finite-volume relative Poincaré theory are substantial components of that program, but they are not yet the completed theorem.

---

## 11. Claim discipline

The following implications must not be silently made:

```text
finite q < 1
  != scale-uniform q < 1

relative distance to TT
  != distance to a unique vacuum line

one positive exact mode
  != global spectral floor

same-root scalar continuum process
  != full 4D continuum Yang--Mills field

real finite-volume resolvent bound
  != complex or continuum resolvent theorem

formal implication machinery
  != discharged raw-model hypothesis
```

The repository should therefore be described as a formalized constructive program with strong theorem chains and sharply localized remaining seams, not as a completed Millennium-prize proof.

---

## 12. Key files near the current frontier

```text
MGAP4D/MathlibAnalytic/

  # completed physical-pair geometry / contraction / decay
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopContraction.lean
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopPowerDecay.lean
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAsymptoticTopProjection.lean
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairFixedSpaceCharacterization.lean

  # non-top coercivity / spectrum / resolvent / Green
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferCoercivity.lean
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPointSpectrumExclusion.lean
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealSpectrumResolvent.lean
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealResolventBound.lean
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopGreenOperator.lean

  # reduced range / relative Poincaré
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairReducedTransferRange.lean
  PeriodicHypercubicEvenSpecialUnitaryPhysicalPairRelativePoincareEstimate.lean

  # exact selected-mode raw-kernel lane
  PhysicalYangMillsWilsonSU2CompletedBoundaryTransferOneSlabMatrixCoefficient.lean
  PhysicalYangMillsWilsonSU2CompletedBoundaryTransferPhysicalModeMatrixCoefficient.lean
```

See `ROADMAP.md` for the ordered next steps.

---

## Validation and repository discipline

The authoritative workflow remains conservative:

```text
start theorem work from the exact canonical SHA
use GitHub-mediated repository operations
never treat queued/in_progress CI as success
freeze writes while exact-head CI is running
inspect terminal failures before editing
keep theorem development additive/tighten-only
forbid sorry / admit / axiom / placeholder declarations
normal-merge only after fresh exact-head success and merge-gate checks
verify merge parents and post-merge canonical CI
```

Current CI runs on the authoritative development line use Lean `4.30.0-rc2` / Lake `5.0.0-src+3dc1a08` at this checkpoint.

---

## What to read next

See [`ROADMAP.md`](ROADMAP.md) for the current ordered proof program, especially the distinction between:

```text
1. the now-completed fixed-finite-volume physical-pair Poincaré theory;
2. the next scale-uniform/global-gap problem;
3. the selected SU(2) raw-kernel exact-mode seam; and
4. the still-open full 4D Yang--Mills continuum construction.
```
