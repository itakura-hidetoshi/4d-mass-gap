# Current proof status

**Updated:** 2026-06-21  
**Main head:** `42223c9a87dc1a8474be95d37abf51299578e9c0`  
**Latest merged proof checkpoint:** PR #288, `59c5780e1efd9e0035aad9bb8c65ff752f5b89dc`  
**Latest merged documentation checkpoint:** PR #291, `d89e8375ab1c5b1dd028829901bc32f92060e0a0`  
**Active proof PRs:** #289 and #282  
**PR #282 head at this snapshot:** `592f3068bbb7f00b3a803ea75a3ed402d6674e3a`

## Status boundary

MGAP4D is a replayable Lean 4 / mathlib formal-development repository. It does **not** yet prove an unconditional four-dimensional continuum Yang--Mills theory, a reconstructed physical Hamiltonian, or a physical mass gap.

The current proof surface has two distinct but complementary lanes:

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
  -> exact Wilson RKHS crossing features
  -> finite tensor-product feature with exact unit norm
  -> bounded integrability from amplitude control
  -> even-periodic local-kernel OS constructors
  -> boundary-fibered Bochner-Gram reflection positivity
```

Open-PR theorems are not part of `main` until merged and replayed.

## Main-branch state

The current `main` head reverts an accidental addition of a PR #282 boundary-fibered file. It therefore makes no net mathematical addition beyond the latest merged proof checkpoint and documentation update.

### Proved or constructed on `main`

#### Finite Gibbs, projection, and Hamiltonian structure

- exact finite Wilson Gibbs and single-link conditional PMFs;
- Gibbs expectation, variance, and heat-bath Dirichlet form;
- conditional expectation projection `P_e` and fluctuation projection `Q_e`;
- detailed balance, symmetry, orthogonality, and weighted Pythagoras;
- concrete finite Gibbs Hilbert realization and normalized vacuum;
- canonical heat-bath Hamiltonian `H_HB = sum_e Q_e`;
- exact quadratic-form identity;
- exact relation `H_HB = |E| (I - P_scan)`.

#### Canonical Dobrushin-to-Rayleigh route

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

Thus the missing finite quantitative input is a physically relevant scale-uniform strict estimate, not a separate `L2`/Rayleigh bridge.

#### Plaquette support and periodic geometry

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
Head: `837feed093504e7f6467933847040b7102fe1972`.

Implemented on the branch:

- physical-link replacement;
- agreement away from one replaced source link;
- signed holonomy congruence;
- non-neighbor locality;
- oriented target-local / target-remote action decomposition.

Still open:

- rebase onto current `main`;
- oriented exact conditional law;
- normalized remote-factor cancellation;
- oriented canonical influence;
- connection to the merged Dobrushin/Rayleigh/Hamiltonian spine.

## Active PR #282 — physical `SU(N)` weak-limit, observable, and OS frontier

State: **open and mergeable**.  
Head: `592f3068bbb7f00b3a803ea75a3ed402d6674e3a`.  
Scale: 459 commits, 141 changed files, `+13289/-0` at this snapshot.

The PR body describes an earlier stable observable checkpoint and is now behind the branch. The branch has since added an exact Wilson RKHS feature layer, bounded-integrability/amplitude constructors, even-periodic crossing-kernel products, and a boundary-fibered reflection-positivity route.

### Current CI receipt

At the recorded head:

- ordinary **PR Lean Fast Check** run **3844** is **in progress**;
- temporary **Boundary-Fibered Pi Measure Check** run **2** completed with an overall **failure**;
- within that temporary run, the targeted step **Build boundary-fibered pi measure factorization** completed successfully;
- the failure was recorded in the final **Propagate build status** step;
- the branch still contains `.github/workflows/tmp-boundary-fibered-pi-measure-check.yml`.

Therefore the current head is not yet merge-ready. The ordinary PR workflow must finish green and the temporary diagnostic workflow must be removed. This is a volatile CI snapshot, not a mathematical theorem statement.

## Concrete finite-volume input in PR #282

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

## Physical weak-limit route in PR #282

`periodicHypercubicSpecialUnitaryPhysicalEmbedding` packages actual finite lattice laws, measurable interpolation into one common Polish carrier, `a_n -> 0`, and `V_n -> infinity`.

Given a proper physical functional `Phi` and

```text
Phi(interpolate_n(A))
  <= (6 * L_n^4)^-1 * S_n(A),
```

`periodicHypercubicSpecialUnitaryWeakLimitOfProperNNRealFunctional` generates:

- pointwise action control;
- uniform Gibbs moment control;
- Markov tails;
- compact containment and tightness;
- Prokhorov subsequence extraction;
- a `PhysicalFourDimensionalYangMillsWeakLimit`;
- convergence of every bounded continuous observable expectation.

This remains conditional on the supplied carrier, interpolation maps, proper functional, and coercive inequality. The reciprocal plaquette scale is a deterministic normalization route, not a physical renormalization theorem.

## Symmetry, observables, and weak-star states in PR #282

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

## Exact Wilson RKHS feature layer in PR #282

The branch constructs a real Hilbert/RKHS feature for the standard `SU(N)` Wilson relative kernel.

### Exact diagonal and norm theorems

The following chain is now formalized:

```text
normalized real trace of identity = 1
  -> Wilson plaquette energy at identity = 0
  -> relative Wilson kernel K_beta(g,g) = 1
  -> ||feature(g)|| = 1.
```

Key theorems in `SpecialUnitaryWilsonKernelFeatureNorm.lean` include:

```lean
normalizedSpecialUnitaryRealTrace_one
specialUnitaryWilsonPlaquetteEnergy_one
specialUnitaryWilsonRelativeKernel_self
RealHilbertKernelFeature.feature_norm_eq_one
specialUnitaryWilsonRelativeKernelFeature_norm_eq_one
localCrossingWilsonKernelConcreteFeature_norm_eq_one
RealHilbertKernelFeature.listProd_feature_norm_eq_one
localCrossingWilsonKernelConcreteFeature_listProd_norm_eq_one
```

The final theorem proves that the finite completed-tensor-product feature of all crossing plaquettes has exact norm one.

### Consequence for weighted features

For

```text
weightedFeature(x) = amplitude(n,F,x) * globalFeature_n(x),
```

Mathlib proves

```text
||weightedFeature(x)|| = |amplitude(n,F,x)|.
```

This removes the need to assume an independent global feature-norm estimate.

## Bounded-integrability and amplitude constructors in PR #282

The current branch packages the analytic route

```text
finite half measure
  + AE strong measurability
  + uniform norm bound
  -> Bochner integrability
  -> Hilbert Gram representation
  -> reflection-form nonnegativity.
```

`PhysicalYangMillsOrientedWilsonOSEvenPeriodicAmplitudeBoundedLocalKernelData` asks for:

- exact local Wilson kernel-product identification;
- finite half measure;
- AE strong measurability of the weighted global feature;
- a scalar amplitude bound

```text
|amplitude(n,F,x)| <= C(n,F).
```

The exact global feature norm one theorem turns this directly into the weighted-feature norm bound required by the finite-measure constructor.

A second factored interface,

```lean
PhysicalYangMillsOrientedWilsonOSEvenPeriodicFactoredAmplitudeBoundedLocalKernelData
```

asks separately for:

- AE strong measurability of the scalar amplitude;
- AE strong measurability of each one-plaquette feature;
- the scalar amplitude bound.

The global feature measurability is generated by the finite completed tensor product, and scalar multiplication gives the weighted feature measurability.

These constructors produce reflection positivity for every approximating lattice state and, by weak-star closure, for the continuum state, provided the explicit half-lattice/kernel data are instantiated.

## Even-periodic local-kernel product frontier

The branch now contains:

- even periodic time reflection;
- crossing-plaquette labels and finite lists;
- local positive-half holonomy interfaces;
- the product of exact local Wilson crossing kernels;
- Hilbert-feature and Bochner-Gram certificates;
- scale-coupling, bounded, amplitude-bounded, and holonomy-measurable constructors;
- transfer to approximating and continuum weak-star reflection positivity.

The remaining issue is not the abstract Gram nonnegativity theorem. It is the exact model-specific identification of the actual periodic `SU(N)` Haar--Gibbs reflection form with the generated kernel-product expression.

## Boundary-fibered reflection-positivity frontier

### Why a boundary fiber is required

Spatial links lying in reflection-fixed time planes are shared by the positive and negative halves. Treating the two halves as fully independent product coordinates would duplicate these variables and give the wrong measure-theoretic shape.

The correct decomposition is boundary-conditioned:

```text
b : BoundaryConfiguration
x,y : open HalfConfiguration

reflection form
  = integral_b integral_x integral_y
      <weightedFeature(b,x), weightedFeature(b,y)>
  = integral_b ||integral_x weightedFeature(b,x)||^2
  >= 0.
```

### Implemented branch infrastructure

The newest files add:

- `FiniteInvolutiveEdgeBoundaryFiberedCoordinates.lean`;
- `FiniteInvolutiveEdgeBoundaryFiberedIndexEquiv.lean`;
- `FiniteInvolutiveEdgeBoundaryFiberedMeasureFactorization.lean`;
- `FiniteInvolutiveEdgeBoundaryFiberedPiMeasure.lean`;
- `FiniteInvolutiveEdgeBoundaryFiberedBochnerFactorization.lean`;
- `PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateConstruction.lean`;
- `PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGram.lean`.

The abstract boundary-fibered certificate proves:

```lean
physical_yang_mills_oriented_boundaryFiberedBochnerGram_pullbackForm_eq_boundary_norm_sq
physical_yang_mills_oriented_boundaryFiberedBochnerGram_pullbackForm_nonneg
physical_yang_mills_oriented_boundaryFiberedBochnerGram_approximating_reflectionPositive
physical_yang_mills_oriented_boundaryFiberedBochnerGram_continuum_reflectionPositive
```

Thus, once the actual Wilson pullback form is identified with the boundary-conditioned iterated inner product, nonnegativity is a boundary integral of squared Bochner moments.

### What remains open in the boundary-fibered layer

- instantiate the exact edge-orbit partition for the periodic even lattice;
- prove the concrete product-Haar disintegration over reflection-fixed boundary variables;
- combine the boundary factorization with the Wilson action splitting and crossing-kernel product;
- prove the actual pullback-form equality required by the certificate;
- discharge boundary-moment square integrability;
- complete ordinary CI validation and remove the temporary workflow.

## Present mathematical frontier

The remaining decisive inputs are:

1. completion of the actual periodic `SU(N)` boundary-fibered Haar/action/kernel factorization;
2. a physically appropriate gauge-compatible distributional carrier;
3. explicit interpolation, blocking, or smearing maps;
4. a justified renormalized coupling trajectory;
5. a proper Sobolev/Besov-type functional with compact sublevels;
6. a uniform coercive interpolation estimate for the actual physical scaling;
7. nontriviality, interacting character, and uniqueness or phase selection;
8. Euclidean covariance, regularity, clustering, and the remaining OS axioms;
9. OS reconstruction and physical transfer-time normalization;
10. a continuum-relevant uniform gap estimate and the physical Hamiltonian mass gap.

Single-link Dobrushin control is expected to describe a restrictive regime. Block dynamics, multiscale estimates, reflection-positive transfer bounds, renormalization-group coercivity, or another scale-uniform mechanism may be required.

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
| Exact local Wilson RKHS feature norm `= 1` | implemented in PR #282 |
| Exact finite global tensor-product feature norm `= 1` | implemented in PR #282 |
| Bounded integrability from finite measure and norm bound | implemented in PR #282 |
| Amplitude-only weighted-feature bound reduction | implemented in PR #282 |
| Factored local measurability -> global measurability | implemented in PR #282 |
| Generic/even-periodic kernel-product OS transfer | implemented in PR #282 under explicit data |
| Boundary-fibered Bochner-Gram nonnegativity | implemented in PR #282 under explicit pullback-form identity |
| Concrete periodic `SU(N)` boundary/Haar/action/kernel identification | incomplete |
| PR #282 current ordinary CI | run 3844 in progress at snapshot |
| Temporary boundary Pi diagnostic | target build step succeeded; overall run failed at status propagation |
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

1. Finish the ordinary PR #282 check on the current boundary-fibered head.
2. Remove the temporary boundary-fibered diagnostic workflow.
3. Complete the exact periodic edge-orbit coordinate and product-Haar boundary disintegration.
4. Identify the actual periodic `SU(N)` Wilson pullback form with the boundary-fibered local-kernel/Bochner-Gram expression.
5. Rebase, audit, and merge the stable compact-gauge, weak-limit, observable, RKHS, and OS layers.
6. Choose the physical carrier, interpolation maps, and renormalized trajectory.
7. Prove the actual coercive compactness estimate and nontriviality.
8. Complete PR #289 and the oriented conditional/influence bridge.
9. Develop a continuum-relevant block, multiscale, reflection-positive-transfer, or renormalization-group estimate.
10. Prove the remaining OS axioms, reconstruct the physical Hamiltonian, and derive a positive gap independently of `exactGapValueReal`.

Lean theorem bodies are authoritative. Open-PR results, conditional hypotheses, selected normalizations, temporary workflows, and internal exact-gap carriers must not be presented as unconditional physical conclusions.
