# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The repository develops two linked theorem lanes:

1. an Osterwalder--Schrader / Hilbert-space / Hamiltonian / spectral lane; and
2. an explicit finite periodic compact-Haar `SU(N)` Wilson / heat-bath / coercivity lane.

They are substantial formal components of a possible proof route. They do **not** yet constitute an unconditional construction of four-dimensional Yang--Mills theory or a proof of the Clay Millennium problem.

```text
Canonical repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Detailed development plan:
  ROADMAP.md

KuuOS reference bridge:
  docs/kuuos_reference_bridge.md
```

## Authoritative status — 2026-07-16 JST

### Latest integrated checkpoint

```text
PR:
  #906 — Extract endpoint fiber covariance and conditional variance

fixed PR head:
  1c00db8252c2d0e1122a4ed02feca72cb06cdc9c

authoritative carrier / squash merge:
  fd1df90beb64e81900444654731f89bb1d42e883

validation:
  PR Lean Fast Check #6230
  run id 29491646991
  success

post-merge comparison:
  fd1df90beb64e81900444654731f89bb1d42e883
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical
```

### Work in progress, not yet integrated

At this snapshot, Draft PR #907, **“Eliminate the endpoint conditional-mean obstruction,”** is based on the exact carrier above.

It evaluates the conditional mean of the target-trajectory endpoint transport through the concrete one-link heat-bath projection. Until that PR is validated and merged, its statements are not active-carrier facts.

## Executive summary

The finite periodic `SU(N)` lane has moved beyond observable oscillation contraction and beyond the first overlap-row estimate.

The active carrier now contains:

```text
exact compact-Haar one-link conditional laws
  -> explicit periodic Dobrushin coefficients
  -> native Gibbs variance and heat-bath Dirichlet identities
  -> a conditional finite Schur/Poincare theorem generator
  -> common-carrier hybrid/native boundary comparison
  -> exact measurable overlap couplings
  -> source-indexed overlap transport rows
  -> finite target-value trajectories across the canonical hybrid path
  -> Gibbs-indexed full endpoint couplings
  -> double-trajectory pair transport
  -> exact endpoint polarization, covariance, and conditional-variance identities.
```

The main finite-volume theorem is still open.

The repository has not yet proved, from the explicit Wilson interaction alone, the observable-specific one-sided profile inequality

```text
u_target(O)
  <= q_target(O)
     + sum_source C(target, source) * u_source(O),
```

where:

- `u` is the canonical hybrid increment profile;
- `q` is the exact native one-link conditional-pair profile; and
- `C` is the explicit periodic `SU(N)` Dobrushin matrix.

PR #854 already proves the finite Schur and bounded-continuous-core Poincaré consequences once that inequality is supplied. The current work is therefore concentrated on the actual transport/correlation theorem needed to generate the inequality without importing it as an assumption.

## What is formally integrated

### 1. Exact lower-spectrum theorem chain from a supplied construction spine

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

The active carrier proves consequences including

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
∃! E : ℝ, IsLeast (σ \ ({0} : Set ℝ)) E
```

These are theorems from the fields of the supplied construction spine. They do not by themselves construct that spine from a concrete four-dimensional gauge approximation family.

### 2. Reconstructed Hamiltonian, PVM support, and bounded-Borel calculus

The repository connects the exact-gap core to the reconstructed vacuum-orthogonal Hamiltonian sector and identifies:

```text
scalar spectral support
  = non-vacuum exact-gap core spectrum

pure PVM open support
  = non-vacuum exact-gap core spectrum.
```

The threshold is characterized by support membership, leastness, and support infimum without requiring a nonzero singleton eigenprojection. Continuous spectral support at the threshold remains compatible with the formal statement.

The bounded-Borel PVM calculus is constructed through:

```text
simple-function integration
  -> uniform bounded-Borel completion
  -> indicator and scalar laws
  -> quadratic scalar spectral measures
  -> symmetry and real-Hilbert polarization
  -> bounded-Borel multiplicativity
  -> operator-norm and vector-level continuity.
```

### 3. Physical semigroup and Hamiltonian coordinate graph

The PVM/Hamiltonian compatibility route proves:

```text
Euclidean scalar Laplace representation
  -> physical semigroup as a PVM exponential
  -> physical PVM difference quotients
  -> canonical restricted coordinate graph
  -> strong continuity from represented Euclidean observables
  -> Hamiltonian derivatives on an observable graph core
  -> graph closure from graph-norm density and generator averages.
```

This reduces opaque assumptions in the reconstruction lane. It still requires an actual nontrivial continuum model supplying the relevant Euclidean, OS, and spectral inputs.

### 4. Explicit periodic compact-Haar `SU(N)` Wilson system

The finite-volume carrier is based on

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ.
```

The integrated interaction route includes:

```text
normalized Haar--Gibbs measure
  -> exact one-link conditional expectations
  -> shared-plaquette localization
  -> mutual conditional-density domination
  -> explicit bounded-test influence coefficients
  -> periodic active-neighbor counting
  -> symmetric volume-independent Dobrushin matrix
  -> finite Schur l2 estimates
  -> one-link variation propagation
  -> random-scan l1 and squared-l2 variation contraction.
```

The explicit coefficients are

```text
eta_beta   = (exp (4 * beta) - 1) / (exp (4 * beta) + 1)
alpha_beta = 18 * eta_beta,
```

with strict contraction in the proved region

```text
beta < log (19 / 17) / 4.
```

These are finite observable-variation theorems. They are not automatically Gibbs `L²` Poincaré theorems and are not automatically compatible with a four-dimensional continuum scaling trajectory.

### 5. Native Gibbs variance and heat-bath Dirichlet identities

On the genuine compact-Haar Gibbs carrier, the repository proves exact identities of the form

```text
Gibbs average of one-link conditional variance
  = ||(I - P_e) O||^2_L2(mu)

sum_e Gibbs average of one-link conditional variance
  = <H_HB O, O>

global independent-pair difference energy
  = 2 Var_mu(O)

one-link conditional independent-pair energy
  = 2 fiber conditional variance

sum_e averaged conditional-pair energy
  = 2 <H_HB O, O>.
```

Thus global variance and local heat-bath energy are represented on compatible continuous compact-group carriers without discretizing `SU(N)` and without identifying pointwise oscillation with conditional variance.

### 6. Conditional finite-volume Poincaré generator

For nonnegative profiles satisfying

```text
u_i <= q_i + sum_j C(i,j) * u_j
```

and `||C||_2 <= alpha < 1`, the integrated finite Schur route proves

```text
(1 - alpha)^2 * sum_i u_i^2 <= sum_i q_i^2.
```

Combined with the exact pair-energy identities, this generates

```text
(1 - alpha_beta)^2 * Var_mu(O)
  <= <H_HB O, O>
```

for bounded continuous observables, **conditional on** the one-sided profile input.

The algebraic and measure-theoretic consequences are integrated. The explicit Wilson interaction has not yet discharged the input for every bounded continuous observable.

### 7. Hybrid/native common carriers and exact overlap transport

The active carrier constructs:

```text
canonical hybrid steps
  -> endpoint pushforward laws
  -> configuration-pair transport couplings
  -> native conditional-pair reference law
  -> off-target boundary carriers
  -> boundary-indexed Markov kernels
  -> common-boundary native resampling
  -> endpoint residual energies
  -> exact overlap/residual couplings of conditional laws
  -> measurable background-indexed overlap kernels
  -> source-indexed L2 transport energies
  -> exact periodic source-row summation.
```

In particular,

```text
sourceOverlapTransportRowEnergy target O
  <= (2 * ||O||)^2 * alpha_beta.
```

The diagonal source and physically inactive sources contribute exactly zero.

This estimate is volume-uniform but uses a global observable amplitude. By itself it is too coarse to close approximate tensorization or the one-sided profile inequality.

### 8. Canonical target trajectories and the full source-row bridge

PRs #884–#900 replace a disconnected collection of fixed-background couplings by a complete finite trajectory across the canonical hybrid ranks.

The integrated route includes:

```text
left-anchored overlap transition kernels
  -> exact recovery of the overlap coupling
  -> history-dependent finite target trajectories
  -> fixed-background transport telescoping
  -> step-dependent source-background transport
  -> background-change residual energies
  -> canonical source-rank support
  -> exact full-rank source-row identification
  -> a Gibbs-pair-indexed trajectory Markov kernel
  -> Gibbs-averaged endpoint trajectory energy.
```

At full rank, the sum of canonical fixed-left overlap fibers is identified exactly with the previously constructed all-source overlap row and with the hybrid boundary residual source-overlap path energy.

The current trajectory square estimate still introduces a factor proportional to the number of physical links. Removing or bypassing such edge-cardinality loss is part of the remaining volume-uniform theorem problem.

### 9. Full endpoint Gibbs self-coupling

PRs #901–#902 reconstruct the first and last trajectory values as full configurations and prove that the global full-rank endpoint law is a genuine Gibbs self-coupling:

```text
map fst Pi_endpoint(target) = gibbsMeasure
map snd Pi_endpoint(target) = gibbsMeasure.
```

Equality of marginals is all that is claimed. It does not imply that the endpoint coupling equals the native conditional-pair law, and it does not determine the sign of their observable cross correlation.

### 10. Double trajectories, polarization, covariance, and conditional variance

PRs #903–#906 introduce two conditionally independent target trajectories over each original independent Gibbs pair and transport the native pair observable across canonical rank.

For each fixed original Gibbs pair `z`, let:

- `T_z` be the single-trajectory endpoint transport;
- `E_single(z)` be its square energy;
- `E_double(z)` be the square energy of the difference of two conditionally independent copies; and
- `m(z)` be the conditional mean of `T_z`.

The active carrier proves the exact iid conditional-variance identity

```text
E_double(z)
  = 2 * E_single(z) - 2 * m(z)^2
  = 2 * Var(T_z).
```

After averaging over the independent Gibbs-pair base,

```text
E_double
  <= 2 * E_single.
```

This improves the earlier factor `4` comparison to factor `2`.

The endpoint polarization layer also isolates the exact cross-moment obstruction. With `N_target(O)` denoting the native one-link conditional-pair energy and `C_target(O)` the endpoint cross moment, the integrated identity has the form

```text
C_target(O)
  = N_target(O)
    - E_single(target,O)
    + GibbsAverage(m(target,z,O)^2).
```

No sign of `C_target(O)` follows merely from equal endpoint marginals or conditional independence. Determining or bypassing this correlation obstruction is the immediate finite-volume frontier.

## Current mathematical frontier

The active proof problem is no longer the construction of a measurable source-path coupling. That carrier now exists.

The next decisive layer is to turn the exact endpoint identities and source-path transport bounds into a **volume-uniform, observable-specific** inequality strong enough to close the one-sided hybrid profile theorem.

The current order is:

```text
evaluate the conditional mean endpoint transport
  -> rewrite the endpoint cross moment in intrinsic Gibbs/heat-bath terms
  -> prove a quantitative sign or correlation bound,
     or construct an alternative comparison avoiding that sign
  -> relate the resulting endpoint/native energy estimate to
     influence-weighted source hybrid increments
  -> remove or bypass edge-cardinality loss
  -> prove u_target <= q_target + sum_source C(target,source) u_source
  -> invoke the integrated finite Schur theorem
  -> obtain bounded-continuous-core Poincare
  -> close the full Gibbs L2 form
  -> obtain a tail-uniform finite-volume gap
  -> transfer coercivity to a concrete continuum OS Hamiltonian.
```

Draft PR #907 addresses the first two arrows. Even if its proposed identities are integrated, the required sign or lower-bound theorem remains a separate obligation.

## Theorem boundary

| Surface | Status on the authoritative carrier |
|---|---|
| Finite Wilson and compact-Haar conditional-law infrastructure | integrated |
| R4 OS reconstruction and completed real Hilbert-space infrastructure | integrated as theorem infrastructure |
| Self-adjoint Hamiltonian and bounded-Borel PVM calculus | integrated |
| Exact lower-spectrum consequences for a supplied construction spine | integrated |
| Reconstructed Hamiltonian/PVM support identification | integrated |
| Explicit periodic `SU(N)` Dobrushin matrix and Schur estimates | integrated |
| Native Gibbs conditional-variance and pair-energy identities | integrated |
| Conditional core Poincaré generator from `u <= q + C u` | integrated |
| Hybrid/native boundary comparison and exact overlap coupling | integrated |
| Canonical source-path trajectory and exact full source-row bridge | integrated |
| Full endpoint Gibbs self-coupling | integrated |
| Double-trajectory polarization, covariance, and conditional variance | integrated through PR #906 |
| Heat-bath projection evaluation of the endpoint conditional mean | Draft PR #907; not integrated at this snapshot |
| Quantitative endpoint cross-correlation/sign theorem | open |
| Volume-uniform observable-specific one-sided profile inequality | open |
| Unconditional bounded-continuous-core periodic `SU(N)` Poincaré theorem | open |
| Full closed Gibbs `L²` Poincaré/form theorem | open |
| Tail-uniform finite-volume gap generated without supplied Rayleigh/Poincaré data | open |
| Transfer of finite coercivity to a continuum OS Hamiltonian | open |
| Continuum scaling family in the required physical regime | open |
| Concrete nontrivial interacting four-dimensional Yang--Mills construction | open |
| Unconditional Clay Millennium existence and mass-gap theorem | not claimed |
| Independent external mathematical consensus | not claimed |

## Exact-gap normalization

`exactGapValueReal` is the public projection of the current Hamiltonian/PVM/spectral exact-gap package. Its exact `33/20` provenance is an internal normalized theorem route.

The repository does not yet derive that value as a physical four-dimensional Yang--Mills mass scale from one specified continuum approximation family.

The following obligations remain distinct:

```text
internal normalization
finite heat-bath coercivity
tail-uniformity
continuum construction
operator/form convergence
continuum spectral transfer
physical-unit normalization
exact physical gap identification.
```

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

The repository also runs a focused **PR Lean Fast Check** for theorem-layer pull requests.

Before treating a result as integrated, verify:

```text
exact PR base
fixed head SHA
successful workflow run
merge commit
post-merge comparison against the authoritative carrier.
```

Open, Draft, stale, superseded, closed-unmerged, or failing PRs are not authoritative-carrier facts.

## Development discipline

The active workflow is:

```text
start from the exact current proof-carrier SHA;
create one focused branch;
open a Draft PR;
run PR Lean Fast Check when the changed paths trigger it;
mark ready only after validation;
squash merge into formal/real-hilbert-uniform-coercive-strong-limit;
verify the merge commit is identical to the carrier head;
start the next theorem unit from the updated carrier.
```

The default `main` branch is the public repository landing surface. Authoritative theorem status is determined by `formal/real-hilbert-uniform-coercive-strong-limit`; documentation on `main` should be synchronized from the validated carrier version.

Additional aliases, wrappers, receipts, smoke files, and handoff structures count as progress only when they expose a necessary dependency, eliminate a supplied assumption, stabilize an actually consumed theorem API, or connect the explicit finite interaction to the continuum Hamiltonian route.
