# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
Authoritative proof carrier: formal/real-hilbert-uniform-coercive-strong-limit
Development roadmap: ROADMAP.md
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Authoritative development status — 2026-07-14 JST

The authoritative proof carrier is:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest integrated checkpoint is:

```text
PR #843 — Prove compact-Haar random-scan variation contraction
PR head 7d017f297b9b35ab5f88945edc88391dc57ab53d
merge commit 8138a2fb7ef84794feb40f4d651efa947de34894
PR Lean Fast Check run #6085 / run id 29305474231 — success
post-merge carrier comparison — identical
```

The repository has advanced substantially beyond the documentation checkpoint at PR #746. The current proof development has two connected fronts:

1. reducing the exact-gap and Hamiltonian/PVM route to actual Euclidean observable, measure, semigroup, and graph-core data; and
2. deriving a volume-uniform finite-lattice coercivity mechanism from the explicit periodic compact-Haar `SU(N)` Wilson interaction.

The decisive unfinished step is to close the genuine Gibbs `L²` conditional-variance estimate and then transfer the resulting finite-volume lower bound along a physically relevant continuum construction.

## What is formally integrated

### 1. Exact lower-spectrum theorem chain

For every supplied

```lean
S : EuclideanYangMillsContinuumMeasureConstructionSpine
```

write

```lean
σ := S.definitionBridge.spine.model.energySpectrum
Δ := exactGapValueReal
E₁ := S.definitionBridge.spine.model.firstExcitation
```

The active carrier proves, among other consequences,

```lean
HasHamiltonianMassGap σ Δ

σ ⊆ ({0} : Set ℝ) ∪ Set.Ici Δ
Set.Ioo 0 Δ ∩ σ = ∅
Δ ∈ σ

IsLeast (σ \ ({0} : Set ℝ)) Δ
sInf (σ \ ({0} : Set ℝ)) = Δ

σ ∩ Set.Iio Δ = ({0} : Set ℝ)
(σ \ ({0} : Set ℝ)) ∩ Set.Iic Δ = ({Δ} : Set ℝ)
σ ∩ Set.Iic Δ = ({0, Δ} : Set ℝ)

E₁ = Δ
IsLeast (σ \ ({0} : Set ℝ)) E₁
∃! E : ℝ, IsLeast (σ \ ({0} : Set ℝ)) E
```

This exact-spectrum layer remains valid and integrated. It is a theorem about every construction spine satisfying the stated fields; it is not by itself a construction of such a spine from a concrete four-dimensional gauge family.

### 2. Exact support through the reconstructed Hamiltonian and PVM

The later carrier no longer leaves the lower-spectrum endpoint only at the abstract certificate level.

PRs #781 and #782 connect the exact-gap core to the actual reconstructed vacuum-orthogonal Hamiltonian sector and prove both

```text
scalar spectral support
  = non-vacuum exact-gap core spectrum
```

and

```text
pure PVM open support
  = non-vacuum exact-gap core spectrum.
```

Consequently `exactGapValueReal` is identified as the least support point and the support infimum without requiring a nonzero singleton eigenprojection. The route is compatible with continuous spectral support at the threshold.

### 3. Constructed bounded-Borel PVM functional calculus

PRs #803 through #820 construct and prove the required functional-calculus laws rather than storing them as independent physical inputs.

The integrated route includes:

```text
simple-function PVM integration
  -> uniform bounded-Borel completion
  -> zero, one, indicator, subtraction, and real-scalar laws
  -> quadratic scalar spectral measure and tail continuity
  -> inner symmetry and real-Hilbert polarization
  -> simple and bounded-Borel multiplicativity
  -> operator-norm and vector-level continuity.
```

In particular, for bounded Borel multipliers `F` and `G`, the completed PVM integral has the theorem-generated algebraic behavior needed downstream, including

```text
I_P(FG) = I_P(F) ∘ I_P(G).
```

### 4. Physical semigroup and Hamiltonian coordinate graph

PRs #821 through #829 reduce the PVM/Hamiltonian compatibility boundary to actual OS and observable data.

The active carrier proves the following route:

```text
scalar Laplace formula + positive PVM support + OS exchange
  -> T_t = I_P(E ↦ exp(-tE) · 1_[0,∞)(E))
  -> physical PVM difference-quotient formula
  -> canonical restricted PVM coordinate graph
  -> strong continuity from Euclidean observable continuity
  -> Hamiltonian-domain derivative from an observable graph core
  -> derivative closure from graph-norm density and contractive generator averages.
```

The strong-continuity input on the whole completed Hilbert space is generated from continuity on represented Euclidean observables, the OS-state isometry, density, and contractivity. PR #827 further derives the observable-norm continuity from dominated convergence for the actual Euclidean realization integrands.

The right derivative on the Hamiltonian domain is likewise no longer taken as one opaque all-domain field: PRs #828 and #829 derive it from an actual observable graph core, Hamiltonian graph-norm density, and a bounded generator-average factorization.

### 5. Explicit periodic compact-Haar `SU(N)` finite-volume route

PRs #830 through #843 establish the current concrete finite-side frontier on the genuine compact gauge carrier

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ.
```

The integrated chain now contains:

```text
periodic SU(N) Wilson system with normalized Haar--Gibbs measure
  -> exact one-link compact-Haar conditional expectations
  -> shared-plaquette localization of the Wilson response
  -> mutual conditional-density domination
  -> explicit bounded-test influence coefficients
  -> periodic shared-plaquette counting for lattice side n ≥ 3
  -> volume-independent Dobrushin row and column bounds
  -> symmetric finite influence matrix
  -> finite Schur ℓ² matrix estimate
  -> one-link propagation of actual observable variations
  -> random-scan total-variation contraction.
```

For the explicit influence profile, the current coefficient is controlled by

```text
18 * eta_beta,
eta_beta = (exp (4 * beta) - 1) / (exp (4 * beta) + 1),
```

and strict contraction follows in the proved region

```text
beta < log (19 / 17) / 4.
```

The exact compact-Haar random-scan observable contracts the finite `ℓ¹` link-variation seminorm at the standard rate

```text
1 - (1 - coefficient) / |Edge|.
```

The symmetric periodic matrix also satisfies the finite Schur estimate

```text
sum_target (sum_source c target source * v source)^2
  <= (18 * eta_beta)^2 * sum_source (v source)^2.
```

The heat-bath/random-scan operator identity and its Poincaré equivalence are integrated on the genuine Gibbs `L²` space:

```text
P_scan = I - |Edge|⁻¹ H_HB.
```

## Current mathematical frontier

The next proof unit is not another wrapper around the exact-gap certificate. It is the analytic bridge from the current pointwise variation theory to the native Gibbs `L²` form.

The immediate sequence is:

```text
PR #841 finite Schur ℓ² matrix estimate
+ PR #842 one-link observable variation propagation
+ PR #843 random-scan observable variation contraction
  -> random-scan ℓ² variation-energy contraction
  -> Gibbs conditional-variance / approximate-tensorization theorem
  -> centered random-scan L² Rayleigh estimate
  -> native heat-bath Poincaré inequality
  -> tail-uniform periodic SU(N) finite-volume coercivity
  -> continuum OS coercivity and spectral lower-bound transfer.
```

The crucial missing implication is therefore not matrix algebra alone. The repository must prove that the concrete observable variation energy controls, or can be completed to, the Gibbs `L²` conditional-variance form with the coefficient required by the random-scan theorem.

A second fundamental boundary is physical scaling. The explicit strict Dobrushin estimate currently lies in a small-`beta` region. The repository does not yet prove that this region follows the four-dimensional continuum weak-coupling scaling trajectory. A final construction must either bridge that regime mismatch or supply another volume-uniform gap mechanism valid along the chosen continuum family.

## The theorem boundary

| Surface | Status on the active carrier |
|---|---|
| Finite Wilson and compact-Haar conditional-law infrastructure | integrated |
| R4 OS reconstruction through completed real Hilbert space | integrated as theorem infrastructure |
| Self-adjoint Hamiltonian and bounded-Borel PVM calculus | integrated |
| Exact lower-spectrum consequences for a supplied construction spine | integrated |
| Exact support identification through the reconstructed Hamiltonian/PVM | integrated |
| Euclidean-observable route to strong continuity and Hamiltonian derivative | integrated through PR #829 |
| Explicit periodic `SU(N)` Dobrushin matrix and strict row/column bounds | integrated through PR #840 |
| Finite Schur `ℓ²` matrix contraction | integrated by PR #841 |
| Actual one-link and random-scan observable variation contraction | integrated by PRs #842–#843 |
| Gibbs `L²` approximate tensorization / centered random-scan Rayleigh theorem from those variations | open |
| Unconditional tail-uniform `SU(N)` heat-bath gap generated from the explicit interaction | open at the analytic bridge |
| Transfer of a uniform finite-volume gap to the continuum OS Hamiltonian | open |
| Continuum scaling family satisfying the required physical regime and all OS/nontriviality inputs | open |
| Unconditional four-dimensional Yang--Mills existence and mass-gap theorem | not claimed |
| Independent external mathematical consensus | not claimed |

## Exact-gap normalization

`exactGapValueReal` is the public projection of the current Hamiltonian/PVM/spectral exact-gap package. Its exact `33/20` provenance is an internal normalized theorem route.

The repository does not yet derive that number as a physical four-dimensional Yang--Mills mass scale from one specified continuum approximation family. Internal normalization, spectral theorem consequences, and physical scale identification remain distinct obligations.

## Replay

Pinned Lean toolchain:

```text
leanprover/lean4:v4.30.0-rc2
```

Pinned mathlib revision:

```text
5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

From a fresh clone:

```bash
lake update
lake build
```

The repository also runs a focused PR Lean Fast Check for each theorem layer.

Before treating a result as integrated, verify the PR base, fixed head SHA, successful check, merge commit, and post-merge comparison against the active carrier.

## Development discipline

The active workflow is:

```text
create one focused branch from the current proof carrier;
open a Draft PR;
run PR Lean Fast Check;
mark ready only after the fixed head succeeds;
squash merge into formal/real-hilbert-uniform-coercive-strong-limit;
verify the merge commit is identical to the carrier head;
start the next theorem layer from the updated carrier.
```

Open, stale, superseded, closed-unmerged, or failing PRs are not active-carrier facts.

Additional aliases, receipts, wrappers, and smoke files count as progress only when they expose a necessary theorem dependency, remove duplicated assumptions, stabilize an actually consumed API, or connect the finite physical construction to the continuum mass-gap route.

The default `main` branch is a repository landing surface. Authoritative theorem integration status is determined by the active proof carrier named above.
