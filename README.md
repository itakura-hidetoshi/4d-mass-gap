# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Current status — 2026-06-18

The current `main` branch is a replayable formal-development and internal-review surface. It is **not** a completed public solution of the four-dimensional Yang--Mills existence and mass-gap problem.

Latest merged checkpoint:

```text
PR #288
commit 59c5780e1efd9e0035aad9bb8c65ff752f5b89dc
Instantiate the orientation-correct finite Z2 Wilson system on the periodic
four-dimensional torus and package
  d_active <= 18,
  m_shared <= 1
for side length n >= 3.
```

Active development at the time of this update:

- PR **#289**: orientation-correct Wilson plaquette locality and target-local/target-remote action decomposition;
- PR **#282**: a genuine `ProbabilityMeasure` weak-limit, tightness, compact-containment, and coercive-moment route on a fixed physical Polish carrier.

The main proof architecture has advanced substantially beyond the former PR #263 documentation. In particular, PR #272 closes the abstract finite-volume route

```text
canonical conditional total variation
  -> Dobrushin variation contraction
  -> centered random-scan spectral/Rayleigh contraction
  -> canonical finite heat-bath Hamiltonian gap.
```

The remaining problem is no longer the abstract Dobrushin-to-Rayleigh implication. The hard frontier is to instantiate the strict coefficient and scaling assumptions in an orientation-correct physical Wilson family and then construct the nontrivial continuum theory.

## Main proof architecture

### 1. Finite Wilson Gibbs, projection, and Hamiltonian lane

On `main`, the finite Wilson lane contains:

```text
finite Wilson action and Gibbs PMF
  -> exact single-link conditional PMF
  -> Gibbs expectation and variance
  -> single-link conditional expectation P_e
  -> fluctuation projection Q_e = I - P_e
  -> exact detailed balance
  -> Gibbs symmetry and orthogonality
  -> Gibbs-weighted Pythagoras
  -> local variance = Gibbs squared norm of Q_e
  -> concrete finite Gibbs Hilbert realization
  -> H_HB = sum_e Q_e
  -> <H_HB x, x> = heat-bath Dirichlet energy
  -> H_HB = |E| (I - P_scan).
```

These finite algebraic and Hilbert-space layers are constructed rather than postulated.

### 2. Canonical Dobrushin-to-Rayleigh lane

PRs #267--#272 construct the canonical finite-volume route from exact conditional laws.

For every finite Wilson system in the legacy finite-system interface, the source defines by finite enumeration:

- the exact off-diagonal conditional total-variation influence;
- the exact zero diagonal;
- exact row sums and the canonical Dobrushin coefficient `alpha_can`;
- a canonical link-variation seminorm and its total-variation form;
- one-update and normalized random-scan variation contraction;
- iterate contraction and centered fixed-point triviality;
- nonconstant eigenvalue bounds;
- a symmetric Gibbs-Hilbert spectral lift;
- the centered random-scan Rayleigh certificate.

Thus the scalar hypothesis

```text
alpha_can < 1
```

automatically produces the finite Dobrushin matrix data, centered Rayleigh contraction, heat-bath coercivity, vacuum-orthogonal Hamiltonian lower bounds, and excitation-eigenvalue lower bounds. The previous documentation statement that

```text
Dobrushin TV row-sum control -> centered Gibbs L2/Rayleigh contraction
```

was still open is obsolete.

What remains open is a physically relevant, scale-uniform proof of `alpha_can < 1` for the intended four-dimensional approximation family.

### 3. Exact plaquette-supported influence lane

PRs #273--#274 localize the finite Wilson influence to the plaquette geometry.

On `main`:

- the Wilson action is split into target-local and target-remote parts;
- the target-remote Boltzmann factor is proved independent of the replacement value and cancels under conditional normalization;
- non-plaquette neighbors have exactly zero conditional total variation and zero canonical influence;
- the diagonal is removed through `activePlaquetteNeighbors`;
- the canonical coefficient satisfies a refined product bound

```text
alpha_can <= d_active * eta_active;
```

- normalized exponential laws satisfy the sharp finite comparison

```text
TV <= (exp R - 1) / (exp R + 1);
```

- source dependence of the target-local action is localized exactly to the shared plaquettes;
- if `m_shared` is the maximum active shared-plaquette multiplicity and `E_max` the maximum plaquette energy, then

```text
eta_active <=
  (exp (2 * beta * m_shared * E_max) - 1) /
  (exp (2 * beta * m_shared * E_max) + 1).
```

Whenever the resulting majorant is below `1 / d_active`, the finite family Hamiltonian-gap and transfer-orbit consequences are generated automatically.

### 4. Concrete periodic four-dimensional geometry

PRs #278 and #281--#288 construct the signed periodic hypercubic geometry and its exact local incidence bounds.

For side length `n >= 3`, `main` proves:

```text
number of active physical-link neighbors <= 18,
number of plaquettes shared by two distinct active links <= 1.
```

The restriction `n >= 3` is essential: at side length two, periodic wrapping can make two distinct parallel links share two plaquettes.

PR #287 introduces `FiniteOrientedLatticeWilsonSystem`, in which configurations assign one group element to each physical positive link and each plaquette boundary separately records forward or backward traversal. It proves:

- signed step gauge covariance;
- plaquette-holonomy conjugation covariance;
- gauge invariance of the orientation-correct Wilson action;
- physical-link plaquette-neighbor, active-neighbor, and shared-plaquette finsets.

PR #288 instantiates this interface for the periodic four-dimensional `Z2` Wilson system and packages the bounds `d_active <= 18` and `m_shared <= 1` into an orientation-correct incidence certificate.

This orientation-aware lane is the preferred physical geometry. The older `FiniteLatticeWilsonSystem` theorems remain valid for the model they define, but the quantitative Gibbs/Dobrushin/Hamiltonian spine has not yet been fully transported to `FiniteOrientedLatticeWilsonSystem` on `main`.

PR #289 begins that migration by adding orientation-correct physical-link replacement, non-neighbor locality, signed holonomy congruence, and target-local/target-remote decomposition.

### 5. Continuum probability-measure lane

The merged source contains typed conditional routes from finite transfer contraction to continuum clustering and OS/Wightman reconstruction. Those routes do not themselves construct the continuum Yang--Mills law.

Open PR #282 adds a more substantive measure-theoretic route:

```text
finite lattice law on a varying configuration type
  -> measurable interpolation into one fixed Polish carrier
  -> pushforward ProbabilityMeasure
  -> coercive moment bound
  -> compact containment
  -> tightness
  -> Prokhorov subsequence
  -> weakly convergent physical continuum ProbabilityMeasure,
     with a_n -> 0 and V_n -> infinity.
```

It also proves convergence of expectations for every bounded continuous observable and inheritance of continuous symmetries that preserve all approximating laws.

The concrete analytic inputs are still open: a suitable gauge-invariant/distributional carrier, interpolation maps, renormalized coupling trajectory, compact-sublevel coercive functional, uniform Wilson moment estimate, nontriviality, uniqueness or phase selection, reflection positivity, Euclidean covariance, clustering, and Schwinger regularity.

## What is proved and what is not

| Surface | Current reading |
|---|---|
| Finite Wilson Gibbs and conditional laws | Constructed on `main` |
| `P_e`, `Q_e`, detailed balance, orthogonality, Pythagoras | Proved on `main` |
| Concrete finite Gibbs Hilbert realization | Constructed on `main` |
| Canonical heat-bath Hamiltonian | Constructed on `main` |
| `H_HB = |E|(I-P_scan)` | Proved on `main` |
| Exact canonical conditional-TV influence matrix | Constructed on `main` |
| Strict canonical Dobrushin coefficient -> centered Rayleigh contraction | Proved on `main` via PR #272 |
| Centered Rayleigh contraction -> finite Hamiltonian gap | Proved on `main` |
| Exact plaquette support of influence | Proved on `main` via PR #274 |
| Sharp normalized-exponential TV bound | Proved on `main` |
| Shared-plaquette action localization | Proved on `main` |
| Periodic 4D active-neighbor bound `<= 18` | Proved on `main` |
| Periodic 4D shared-plaquette multiplicity `<= 1` for `n >= 3` | Proved on `main` |
| Orientation-correct finite Wilson system and periodic `Z2` instance | Constructed on `main` |
| Orientation-correct locality/conditional-law bridge | In progress in PR #289 |
| Uniform strict Dobrushin bound along a continuum family | Not proved |
| Non-Abelian orientation-correct quantitative family | Not yet constructed |
| Physical heat-bath/transfer normalization | Not dynamically derived |
| Genuine weak-limit framework on a fixed physical carrier | Implemented in open PR #282, not yet on `main` |
| Concrete nontrivial continuum Yang--Mills measure | Not proved |
| OS/Wightman analytic hypotheses | Not discharged |
| Physical mass gap | Open |
| Independent physical derivation of `33/20` | Open |
| External mathematical consensus | Not claimed |

## Quantitative interpretation of the present geometry

The merged geometry supplies the finite constants

```text
d_active <= 18,
m_shared <= 1
```

for the periodic four-dimensional physical-link lattice with `n >= 3`. Combined with the merged abstract plaquette estimate, this identifies the exact next formal target: transport the orientation-correct system into the conditional-law/Dobrushin spine and specialize the plaquette energy bound.

For the current `Z2` instance, the plaquette energy is defined to be `0` or `1`. The final theorem that packages this fact as the required `E_max`, inserts the `18` and `1` bounds, and derives a strict canonical coefficient has not yet been merged.

Moreover, the resulting single-link Dobrushin condition is expected to be a restrictive small-`beta` regime. It should not be confused with the weak-coupling continuum scaling regime. A successful continuum route may therefore require block dynamics, multiscale estimates, or a different coercive mechanism even after the finite `Z2` specialization is closed.

## Exact `33/20` lane

The source carries the normalized value `33/20` through internal Hamiltonian/PVM/spectral and R6--R7 audit interfaces.

```text
HamiltonianPVMSpectralExactGapValue.lean
  defines hamiltonianPVMSpectralNormalized3320Value := 33/20

ExactGapReal.lean
  projects exactGapValueReal from that package

later spectral / R6 / R7 files
  transport and audit the same carried value.
```

This is a typed normalization and dependency-routing surface. It is **not** an independent derivation of the physical four-dimensional Yang--Mills mass gap. Read `docs/exact_gap_layer_separation.md` for the dependency-level account.

## Primary review anchors

| Topic | File |
|---|---|
| Short status anchor | `docs/current_proof_status.md` |
| Development roadmap | `ROADMAP.md` |
| Canonical Dobrushin spectral/Rayleigh lift | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonCanonicalRandomScanRayleighSpectralLift.lean` |
| Canonical strict-family gap | `MGAP4D/MathlibAnalytic/FiniteWilsonCanonicalDobrushinStrictFamilyGap.lean` |
| Target-local/remote decomposition | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonActionLocalDecomposition.lean` |
| Conditional plaquette support | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonConditionalPlaquetteSupport.lean` |
| Active plaquette profile | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonActivePlaquetteDobrushinProfile.lean` |
| Shared-plaquette energy bound | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonSharedPlaquetteEnergyGap.lean` |
| Signed periodic geometry | `MGAP4D/MathlibAnalytic/PeriodicHypercubicSignedGeometry.lean` |
| Active-neighbor bound | `MGAP4D/MathlibAnalytic/PeriodicHypercubicActiveNeighborBound.lean` |
| Shared-plaquette uniqueness | `MGAP4D/MathlibAnalytic/PeriodicHypercubicSharedPlaquetteUniqueness.lean` |
| Orientation-correct finite Wilson system | `MGAP4D/MathlibAnalytic/FiniteOrientedLatticeWilsonSystem.lean` |
| Periodic oriented `Z2` instance | `MGAP4D/MathlibAnalytic/Z2PeriodicHypercubicOrientedWilsonSystem.lean` |
| Exact-gap dependency separation | `docs/exact_gap_layer_separation.md` |
| Placeholder / proof-debt inventory | `docs/proof_placeholder_inventory.md` |

## Replay

Pinned toolchain:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

From a fresh clone:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
bash scripts/check.sh
lake build
```

A successful replay means that the declared Lean files and audit scripts build in the pinned environment. It is reproducibility evidence, not external certification of the physical theorem.

## Current priorities

1. Merge and verify the orientation-correct locality layer in PR #289.
2. Transport the exact single-link conditional law, canonical influence, Dobrushin contraction, and Hamiltonian-gap spine to `FiniteOrientedLatticeWilsonSystem`.
3. Specialize the periodic `Z2` energy bound and connect `d_active <= 18`, `m_shared <= 1` to an explicit strict-coefficient theorem.
4. Determine rigorously whether single-link Dobrushin estimates can serve any continuum scaling regime; otherwise construct a block or multiscale replacement.
5. Generalize the orientation-correct quantitative lane beyond finite `Z2` to the intended compact non-Abelian gauge group.
6. Merge and instantiate the physical weak-limit framework of PR #282 with concrete uniform analytic estimates.
7. Derive the physical transfer-time/generator normalization independently of `exactGapValueReal`.
8. Prove nontrivial continuum convergence, clustering, and the analytic OS/Wightman hypotheses, followed by independent review.

## Public claim boundary

Recommended wording:

```text
MGAP4D is a Lean 4 formal-development repository for a four-dimensional
Yang--Mills mass-gap proof architecture. It contains concrete finite Wilson
Gibbs, projection, Gibbs-Hilbert and heat-bath Hamiltonian constructions; an
exact canonical Dobrushin-to-centered-Rayleigh theorem; exact plaquette-supported
influence estimates; and an orientation-correct periodic four-dimensional Z2
geometry with active degree at most 18 and shared-plaquette multiplicity at most
one for side length at least three. Work is continuing on the orientation-correct
conditional-law bridge, scale-uniform physical estimates, weak continuum limits,
physical transfer normalization, and OS/Wightman reconstruction. The repository
does not currently establish an unconditional continuum Yang--Mills theory or a
physical mass gap, and it does not independently derive the normalized value
33/20.
```
