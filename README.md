# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
Authoritative proof carrier: formal/real-hilbert-uniform-coercive-strong-limit
Development roadmap: ROADMAP.md
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Authoritative development status — 2026-07-15 JST

The authoritative proof carrier is:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest integrated checkpoint is:

```text
PR #881 — Sum periodic SU(N) hybrid source overlap transport rows
PR head 15b21a6bdb8237161749f018a149322efc550980
merge commit 96a4650e4bf34eb89c36720b14966fb83a049991
PR Lean Fast Check #6175 / run id 29405234819 — success
post-merge carrier comparison — identical
```

The repository has advanced beyond the PR #843 observable-variation checkpoint. The finite-volume lane now contains the native Gibbs conditional-variance identities, a Schur-resolvent route that generates a bounded-continuous-core Poincaré inequality from one explicit one-sided profile estimate, and an actual compact-Haar hybrid/native coupling construction through measurable overlap kernels and source-indexed transport energies.

The immediate unfinished theorem is no longer “identify oscillation variation with conditional variance.” The current target is the observable-specific one-sided coupling inequality

```text
u_target(O)
  <= q_target(O)
     + sum_source C(target, source) * u_source(O),
```

where `u` is the canonical hybrid increment profile, `q` is the exact native conditional-pair profile, and `C` is the explicit periodic `SU(N)` Dobrushin matrix. PR #854 proves that this inequality would generate the bounded-continuous-core heat-bath Poincaré estimate with gap `(1 - alpha_beta)^2`.

PRs #855–#881 build the measure-theoretic and transport machinery needed to prove that inequality. The present source-overlap row estimate still carries the global amplitude `(2 * ‖O‖)^2`; it has not yet been converted into the source hybrid profile or assembled into the endpoint residual energies. That observable-specific replacement is the active frontier.

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

This is a theorem about every construction spine satisfying the stated fields. It is not by itself a construction of such a spine from a concrete four-dimensional gauge family.

### 2. Reconstructed Hamiltonian and PVM support

The exact-gap core is connected to the actual reconstructed vacuum-orthogonal Hamiltonian sector. The integrated route identifies both

```text
scalar spectral support
  = non-vacuum exact-gap core spectrum
```

and

```text
pure PVM open support
  = non-vacuum exact-gap core spectrum.
```

The threshold can therefore be characterized as the least support point and support infimum without assuming a nonzero singleton eigenprojection. Continuous spectral support at the threshold remains compatible with the formal statement.

### 3. Constructed bounded-Borel PVM calculus

PRs #803–#820 construct the functional calculus consumed by the physical semigroup route:

```text
simple-function PVM integration
  -> uniform bounded-Borel completion
  -> zero, one, indicator, subtraction, and real-scalar laws
  -> quadratic scalar spectral measures and tail continuity
  -> symmetry and real-Hilbert polarization
  -> simple and bounded-Borel multiplicativity
  -> operator-norm and vector-level continuity.
```

For bounded Borel multipliers `F` and `G`, the completed integral satisfies the theorem-generated multiplicative law

```text
I_P(FG) = I_P(F) ∘ I_P(G).
```

### 4. Physical semigroup and Hamiltonian coordinate graph

PRs #821–#829 connect the PVM/Hamiltonian compatibility boundary to Euclidean measure and observable data:

```text
scalar Laplace formula + positive PVM support + OS exchange
  -> physical semigroup as a PVM exponential
  -> physical PVM difference quotients
  -> canonical restricted PVM coordinate graph
  -> strong continuity from Euclidean observable continuity
  -> Hamiltonian-domain derivatives from an observable graph core
  -> derivative closure from graph-norm density and contractive generator averages.
```

Whole-space strong continuity is generated from represented Euclidean observables, the OS-state isometry, density, and contractivity. The Hamiltonian derivative is generated from an actual observable graph core rather than stored as one opaque all-domain field.

### 5. Explicit periodic compact-Haar `SU(N)` interaction

The concrete finite-volume carrier is

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ.
```

PRs #830–#845 establish:

```text
periodic SU(N) Wilson system with normalized Haar--Gibbs measure
  -> exact one-link compact-Haar conditional expectations
  -> shared-plaquette localization
  -> mutual conditional-density domination
  -> explicit bounded-test influence coefficients
  -> periodic shared-plaquette counting for n >= 3
  -> symmetric volume-independent Dobrushin matrix
  -> finite Schur l2 estimate and resolvent coercivity
  -> actual one-link variation propagation
  -> random-scan l1 and squared-l2 variation contraction.
```

The explicit coefficient is

```text
eta_beta = (exp (4 * beta) - 1) / (exp (4 * beta) + 1)
alpha_beta = 18 * eta_beta,
```

with strict contraction in the proved region

```text
beta < log (19 / 17) / 4.
```

The actual random-scan observable has:

```text
total-variation contraction rate
  1 - (1 - alpha_beta) / |Edge|
```

and squared variation-energy contraction rate

```text
(1 - (1 - alpha_beta) / |Edge|)^2.
```

These are observable oscillation-profile theorems. They are not, by themselves, Gibbs `L²` Poincaré theorems.

### 6. Native Gibbs conditional-variance and independent-pair identities

PRs #847, #849, and #850 prove the exact observable-core identities on the genuine compact-Haar Gibbs carrier:

```text
Gibbs average of one-link conditional variance
  = ‖(I - P_e) O‖²_L2(mu),

sum_e Gibbs average of one-link conditional variance
  = <H_HB O, O>,

∫ (O(A) - O(B))² d(mu x mu)
  = 2 Var_mu(O),

conditional independent-pair energy at e
  = 2 fiber conditional variance,

sum_e averaged conditional-pair energy
  = 2 <H_HB O, O>.
```

Thus the global variance side and the local Dirichlet side are represented on compatible genuine pair carriers without discretizing `SU(N)` and without identifying pointwise oscillation with conditional variance.

### 7. Conditional finite-volume core Poincaré generator

PRs #848 and #851–#854 prove the finite algebra and theorem packaging needed after one measure-theoretic coupling estimate.

For nonnegative profiles satisfying

```text
u_i <= q_i + sum_j C(i,j) * u_j
```

and `‖C‖_2 <= alpha < 1`, the integrated route proves

```text
(1 - alpha)^2 * sum_i u_i^2 <= sum_i q_i^2.
```

The canonical independent-Gibbs hybrid path supplies the global pair-energy majorant, and `q_i^2` is exactly the native conditional-pair energy. Consequently the one-sided profile input generates

```text
(1 - alpha_beta)^2 * Var_mu(O)
  <= <H_HB O, O>
```

for bounded continuous observables.

This is an integrated theorem generator from the stated one-sided profile input. The repository has not yet proved that input for every bounded continuous observable.

### 8. Actual hybrid/native coupling and boundary transport

PRs #855–#874 build the actual law-comparison carrier:

```text
hybrid steps as exact single-link replacements
  -> centered endpoint fluctuation decomposition
  -> endpoint pushforward laws
  -> configuration-pair transport coupling
  -> native conditional-pair reference law on the same carrier
  -> exact global and local pair-energy identifications
  -> off-target boundary carrier and diagonal support
  -> boundary-indexed conditional Markov kernels
  -> kernel composition, absolute-continuity reflection, and RN derivatives
  -> common-boundary resampling coupling
  -> integrated three-term fluctuation-energy decomposition
  -> boundary-fiber disintegration
  -> endpoint residual energies as observable transport energies.
```

The principal integrated decomposition has the form

```text
hybridIncrementEnergy
  <= 3 * (
       firstResidualEnergy
       + hybridBoundaryResampledConditionalPairEnergy
       + secondResidualEnergy).
```

No equality between the hybrid boundary law and the Gibbs boundary law is assumed.

### 9. Exact compact-Haar overlap coupling and source transport rows

PRs #875–#881 construct a quantitative overlap coupling of two exact one-link conditional laws:

```text
common overlap density + residual densities
  -> exact coupling with correct marginals
  -> sharp residual-mass bound from mutual likelihood-ratio domination
  -> mismatch-probability control
  -> L2 observable transport-energy control
  -> measurable background-indexed overlap-coupling kernel
  -> integration along a canonical source-link hybrid step
  -> specialization to the actual periodic SU(N) shared-plaquette influence
  -> exact diagonal zero and full source-row summation.
```

For each target link, the current periodic theorem proves

```text
sourceOverlapTransportRowEnergy target O
  <= (2 * ‖O‖)^2 * alpha_beta.
```

It also proves exact zero for the diagonal source and for sources outside the physical active-neighbor set.

This closes the explicit likelihood-ratio-to-transport row. It does not yet prove the observable-specific endpoint residual estimate needed by the one-sided profile inequality.

## Current mathematical frontier

The next proof unit must use the integrated coupling objects to replace the global amplitude estimate by the actual source hybrid increment profile.

A viable theorem order is:

```text
source-step overlap coupling
  -> observable-specific source transport estimate
  -> endpoint residual energy <= influence-weighted source hybrid energies
  -> square-root/Minkowski conversion
  -> u_target <= q_target + C u
  -> PR #854 finite Schur theorem
  -> bounded-continuous-core heat-bath Poincaré
  -> closure to the full Gibbs L2 domain
  -> tail-uniform finite-volume coercivity.
```

Two distinctions must remain explicit:

1. The current row bound by `(2 * ‖O‖)^2 * alpha_beta` is volume-uniform but too coarse to close approximate tensorization. It must be replaced by an observable-local source-energy bound.
2. A bounded-continuous-core Poincaré theorem is not yet the full closed-form Gibbs `L²` theorem. Density, form closure, and compatibility with the native heat-bath Hamiltonian domain must be completed after the profile estimate.

The subsequent physical boundary is unchanged: the present strict Dobrushin estimate lies in a small-`beta` region. The repository does not yet prove that this region follows the four-dimensional continuum scaling trajectory. Either the regime must be connected to the selected continuum family, or a different volume-uniform gap mechanism must be supplied.

## Theorem boundary

| Surface | Status on the active carrier |
|---|---|
| Finite Wilson and compact-Haar conditional-law infrastructure | integrated |
| R4 OS reconstruction through completed real Hilbert space | integrated as theorem infrastructure |
| Self-adjoint Hamiltonian and bounded-Borel PVM calculus | integrated |
| Exact lower-spectrum consequences for a supplied construction spine | integrated |
| Reconstructed Hamiltonian/PVM support identification | integrated |
| Euclidean-observable route to strong continuity and Hamiltonian differentiation | integrated through PR #829 |
| Explicit periodic `SU(N)` Dobrushin matrix, row/column bounds, and Schur estimates | integrated |
| Random-scan `l1` and squared-`l2` observable variation contraction | integrated through PR #845 |
| Native Gibbs conditional-variance and independent-pair energy identities | integrated |
| Conditional core Poincaré generator from `u <= q + C u` | integrated through PR #854 |
| Hybrid/native common-carrier, boundary-kernel, and resampling decomposition | integrated through PR #874 |
| Exact overlap coupling, residual-mass influence, and source transport row | integrated through PR #881 |
| Observable-specific endpoint residual estimate yielding `u <= q + C u` | open — immediate frontier |
| Unconditional bounded-continuous-core periodic `SU(N)` Poincaré inequality | open at the one-sided profile input |
| Full Gibbs `L²` Poincaré/form theorem from the explicit interaction | open |
| Tail-uniform finite-volume gap generated without external Rayleigh/Poincaré data | open |
| Transfer of finite coercivity to a continuum OS Hamiltonian | open |
| Continuum scaling family satisfying the required physical regime and OS/nontriviality inputs | open |
| Unconditional four-dimensional Yang--Mills existence and mass-gap theorem | not claimed |
| Independent external mathematical consensus | not claimed |

## Exact-gap normalization

`exactGapValueReal` is the public projection of the current Hamiltonian/PVM/spectral exact-gap package. Its exact `33/20` provenance is an internal normalized theorem route.

The repository does not yet derive that value as a physical four-dimensional Yang--Mills mass scale from one specified continuum approximation family. Internal normalization, spectral theorem consequences, finite heat-bath coercivity, continuum transfer, and physical scale identification remain distinct obligations.

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

The default `main` branch is the public repository landing surface. Authoritative theorem integration status is determined by the active proof carrier named above.
