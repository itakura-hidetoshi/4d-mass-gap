# Current proof status

**Updated:** 2026-06-20  
**Main head:** `017ad8ea96346100af31af114f69380c6194d8e1` (PR #290, documentation)  
**Latest merged proof checkpoint:** PR #288, `59c5780e1efd9e0035aad9bb8c65ff752f5b89dc`  
**Active proof PRs:** #289 and #282

## Status boundary

MGAP4D is a replayable formal-development repository. It does **not** yet prove an unconditional four-dimensional continuum Yang--Mills theory, a reconstructed physical Hamiltonian, or a physical mass gap.

The current proof surface has two distinct lanes:

```text
main:
finite Wilson Gibbs law
  -> exact conditionals and projections
  -> Gibbs Hilbert space and heat-bath Hamiltonian
  -> canonical Dobrushin influence
  -> centered Rayleigh contraction
  -> finite Hamiltonian-gap consequences
  -> plaquette-supported influence
  -> periodic oriented four-dimensional incidence bounds

open PR #282:
signed periodic SU(N) Haar--Gibbs laws
  -> gauge invariance and normalized action bound
  -> coercive moment / tightness / Prokhorov subsequence
  -> physical weak-limit package on one Polish carrier
  -> gauge-symmetry and observable transfer
  -> gauge-invariant continuous and weak-star states
  -> conditional OS reflection-positivity transfer
```

Open-PR theorems are not part of `main` until merged and replayed.

## Proved on `main`

### Finite Gibbs, projection, and Hamiltonian structure

- exact finite Wilson Gibbs and single-link conditional PMFs;
- Gibbs expectation, variance, and heat-bath Dirichlet form;
- conditional expectation projection `P_e` and fluctuation projection `Q_e`;
- detailed balance, symmetry, orthogonality, and weighted Pythagoras;
- concrete finite Gibbs Hilbert realization and normalized vacuum;
- canonical heat-bath Hamiltonian `H_HB = sum_e Q_e`;
- exact quadratic-form identity;
- exact relation `H_HB = |E| (I - P_scan)`.

### Canonical Dobrushin-to-Rayleigh route

PRs #267--#272 prove:

- exact off-diagonal conditional-TV influence and zero diagonal;
- exact row sums and canonical coefficient `alpha_can`;
- minimality among admissible Dobrushin matrices;
- link-variation and total-variation seminorms;
- one-update and normalized random-scan contraction;
- iterate contraction and centered fixed-point triviality;
- nonconstant eigenvalue control;
- symmetric Gibbs-Hilbert spectral lift;
- centered random-scan Rayleigh contraction;
- automatic finite Hamiltonian and excitation bounds from `alpha_can < 1`.

Thus the missing finite quantitative input is a physically relevant strict estimate, not a separate `L2`/Rayleigh bridge.

### Plaquette support and periodic geometry

PRs #273--#274 prove:

```text
alpha_can <= d_active * eta_active,

eta_active <=
  (exp (2 * beta * m_shared * E_max) - 1) /
  (exp (2 * beta * m_shared * E_max) + 1).
```

They also prove exact zero influence outside plaquette support, remote-factor cancellation, and exact localization to shared plaquettes.

PRs #278 and #281--#288 construct signed periodic four-dimensional geometry and prove, for `n >= 3`,

```text
d_active <= 18,
m_shared <= 1.
```

PR #287 adds the orientation-correct finite Wilson system; PR #288 adds the periodic oriented `Z2` instance and incidence certificate.

## Active PR #289 — oriented locality bridge

State: **open and mergeable**.  
Head at this snapshot: `837feed093504e7f6467933847040b7102fe1972`.

Implemented on the branch:

- physical-link replacement;
- agreement away from one replaced source link;
- signed holonomy congruence;
- non-neighbor locality;
- oriented target-local / target-remote action decomposition.

Still open:

- rebase onto the current `main`;
- oriented exact conditional law;
- normalized remote-factor cancellation;
- oriented canonical influence;
- connection to the merged Dobrushin/Rayleigh/Hamiltonian spine.

## Active PR #282 — physical `SU(N)` weak-limit and OS frontier

State: **open and mergeable**.  
Head at this snapshot: `ceb2d9b5ba4f186ba98e914982ff5e1b5598bd13`.  
Scale: 301 commits, 111 changed files, +8752/-2 at the snapshot.

### Current CI receipt

PR Lean Fast Check run **3687** completed with **failure**. The failure is localized to

```text
MGAP4D/MathlibAnalytic/RealHilbertKernelFeatureProduct.lean:68:2
Type mismatch when assigning motive:
a Type-valued finite kernel-product construction was elaborated where a
Prop-valued motive was expected.
```

In the same run, the weak-limit, gauge-symmetry, observable, weak-star state, reflection-positivity transfer, oriented Wilson OS pullback, Hilbert-Gram, Bochner-Gram, kernel-feature, half-lattice/Peter--Weyl, and terminal OS-construction files all built successfully. The current head is therefore not green, but the stopping error is one explicit generic Hilbert-kernel product helper rather than a failure of the already compiled physical weak-limit or OS transfer files.

The head temporarily enables diagnostic log capture in the PR workflow. That workflow change must be removed after the proof repair and before merge.

### Concrete finite-volume input

The branch constructs actual finite-volume probability laws, not only an abstract convergence wrapper:

- one configuration variable per positive physical link;
- signed forward/backward plaquette traversal;
- finite oriented compact gauge Wilson systems;
- normalized compact Haar product measure;
- Wilson Gibbs tilt as a `ProbabilityMeasure`;
- finite-volume gauge invariance;
- periodic four-dimensional geometry bridge;
- exact counts

```text
#Vertex(L) = L^4,
#AxisPair = 6,
#Plaquette(L) = 6 * L^4;
```

- specialization to `SU(N)`;
- standard energy

```text
E_W(U) = 1 - Re(trace U) / N,
0 <= E_W(U) <= 2;
```

- deterministic normalized action bound

```text
(6 * L^4)^-1 * S_L(A) <= 2.
```

### Physical weak-limit route

`periodicHypercubicSpecialUnitaryPhysicalEmbedding` packages actual finite lattice laws, measurable interpolation into one common Polish carrier, `a_n -> 0`, and `V_n -> infinity`.

Given a proper physical functional `Phi` and

```text
Phi(interpolate_n(A))
  <= (6 * L_n^4)^-1 * S_n(A),
```

`periodicHypercubicSpecialUnitaryWeakLimitOfProperNNRealFunctional` generates:

- pointwise action control;
- uniform moment control;
- Markov tails;
- compact containment and tightness;
- Prokhorov subsequence extraction;
- a `PhysicalFourDimensionalYangMillsWeakLimit`;
- convergence of every bounded continuous observable expectation.

This is conditional on the supplied carrier, interpolation maps, proper functional, and coercive inequality. The reciprocal plaquette scale is a deterministic normalization route, not a physical renormalization theorem.

### Symmetry, observables, and weak-star states

Under a continuous physical action and interpolation equivariance, the branch proves

```text
map(action g, mu_YM) = mu_YM.
```

Consequences include:

- invariant finite and continuum event probabilities;
- invariant laws of arbitrary measurable observables;
- invariant bounded-continuous expectations;
- invariant two-point and connected correlations;
- finite n-point invariance and convergence;
- a real subalgebra of gauge-invariant bounded continuous observables;
- normalized positive continuous expectation states;
- weak-star convergence of lattice states to the continuum state.

### OS reflection-positivity frontier

The branch proves generic closure and packaging results:

```text
positive-time observable algebra and reflection
  + exact half-lattice measure/action decomposition
  + Peter--Weyl Hilbert-feature factorization
  -> finite-lattice reflection positivity
  -> weak-star limit transfer
  -> continuum reflection-positive state.
```

Implemented interfaces/theorems include:

- weak-star closedness of reflection positivity;
- bridge from finite Wilson OS certificates to physical lattice states;
- oriented Wilson pullback form;
- kernel-quadratic and Hilbert-feature certificates;
- terminal `PhysicalYangMillsContinuumOSPositiveStatePackage`.

The branch does **not** yet supply the complete concrete periodic `SU(N)` half-lattice decomposition and Peter--Weyl/character certificate. The generic finite-product Hilbert-feature helper must also be repaired before the head is green.

## Present mathematical frontier

The remaining decisive inputs are:

1. a physically appropriate gauge-compatible distributional carrier;
2. explicit interpolation, blocking, or smearing maps;
3. a justified renormalized coupling trajectory;
4. a proper Sobolev/Besov-type functional with compact sublevels;
5. a uniform coercive interpolation estimate for the actual physical scaling;
6. concrete periodic `SU(N)` half-lattice and Peter--Weyl reflection-positivity data;
7. nontriviality, interacting character, and uniqueness or phase selection;
8. Euclidean covariance, regularity, clustering, and the remaining OS axioms;
9. OS reconstruction and physical transfer-time normalization;
10. a continuum-relevant uniform gap estimate and the physical Hamiltonian mass gap.

Single-link Dobrushin control is expected to describe a restrictive regime. Block dynamics, multiscale estimates, reflection-positive transfer bounds, or another scale-uniform mechanism may be required.

## Claim table

| Claim | Status |
|---|---|
| Finite Gibbs/projection/Hilbert/Hamiltonian spine | proved or constructed on `main` |
| Exact canonical Dobrushin matrix | constructed on `main` |
| `alpha_can < 1` -> centered Rayleigh contraction | proved on `main` |
| Exact plaquette support and shared-plaquette majorant | proved on `main` |
| Periodic bounds `d_active <= 18`, `m_shared <= 1` | proved on `main` for `n >= 3` |
| Orientation-correct finite Wilson system and periodic `Z2` instance | constructed on `main` |
| Orientation-correct locality bridge | open in PR #289 |
| Oriented conditional/influence/Hamiltonian bridge | incomplete |
| Explicit periodic `Z2` strict-coefficient theorem | open |
| Compact oriented Haar--Gibbs and standard `SU(N)` finite law | implemented in PR #282 |
| Concrete signed periodic `SU(N)` weak-limit constructor | implemented in PR #282 under explicit analytic inputs |
| Gauge-symmetry, observable, correlation, and n-point transfer | implemented in PR #282 under compatibility inputs |
| Gauge-invariant continuous and weak-star state convergence | implemented in PR #282 |
| Generic OS reflection-positivity limit transfer | implemented in PR #282 |
| PR #282 latest head | failing at `RealHilbertKernelFeatureProduct.lean:68:2` |
| Concrete periodic `SU(N)` half-lattice/Peter--Weyl OS certificate | incomplete |
| Concrete physical carrier/interpolation/renormalized trajectory | open |
| Nontrivial interacting continuum measure | open |
| Full OS reconstruction | open |
| Physical Hamiltonian mass gap | open |
| Independent physical derivation of `33/20` | open |
| External mathematical consensus | not claimed |

## Exact `33/20` dependency

`HamiltonianPVMSpectralExactGapValue.lean` defines the normalized internal value `33/20`; `ExactGapReal.lean` projects `exactGapValueReal`; later spectral and R6--R7 files transport the same value.

This is an internal normalization and dependency-routing lane, not an independent physical derivation.

## Next actions

1. Repair the Type-valued recursive motive in `RealHilbertKernelFeatureProduct.lean` and rerun the ordinary PR check.
2. Remove the temporary diagnostic workflow change.
3. Instantiate the concrete periodic `SU(N)` half-lattice and Peter--Weyl OS inputs.
4. Rebase, audit, and merge the stable compact-gauge/weak-limit spine.
5. Choose the physical carrier, interpolation maps, and renormalized trajectory.
6. Prove the actual coercive compactness estimate and nontriviality.
7. Complete PR #289 and the oriented conditional/influence bridge.
8. Develop a continuum-relevant block, multiscale, or transfer estimate.
9. Prove the remaining OS axioms, reconstruct the physical Hamiltonian, and derive a positive gap independently of `exactGapValueReal`.

Lean theorem bodies are authoritative. Open-PR results, conditional hypotheses, selected normalizations, diagnostic workflows, and internal exact-gap carriers must not be presented as unconditional physical conclusions.
