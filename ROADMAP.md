# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-06-18

Latest merged checkpoint:

```text
PR #288
commit 59c5780e1efd9e0035aad9bb8c65ff752f5b89dc
```

Active pull requests:

- **#289** — orientation-correct Wilson plaquette locality;
- **#282** — physical weak limits on a fixed Polish carrier.

The repository is a replayable formal-development surface. It does not yet prove an unconditional four-dimensional Yang--Mills continuum theory or physical mass gap.

## Completed on `main`

### 1. Finite Gibbs and Hamiltonian spine

- [x] finite Wilson Gibbs PMF and exact single-link conditional laws;
- [x] Gibbs expectation, variance, and heat-bath Dirichlet form;
- [x] conditional-expectation projection `P_e` and fluctuation projection `Q_e`;
- [x] detailed balance, Gibbs symmetry, orthogonality, and Pythagoras;
- [x] concrete finite Gibbs Hilbert realization and normalized vacuum;
- [x] canonical heat-bath Hamiltonian `H_HB = sum_e Q_e`;
- [x] exact quadratic-form identity;
- [x] exact scaling `H_HB = |E| (I - P_scan)`;
- [x] centered Rayleigh contraction implies finite Poincare and Hamiltonian gaps.

### 2. Canonical Dobrushin-to-Rayleigh theorem

PRs #267--#272 close the abstract finite-volume chain:

```text
exact conditional TV influence
  -> canonical Dobrushin coefficient alpha_can
  -> link-variation contraction
  -> random-scan iterate contraction
  -> centered fixed-point triviality
  -> eigenvalue control
  -> Gibbs-Hilbert spectral lift
  -> centered Rayleigh contraction
  -> finite Hamiltonian gap.
```

- [x] exact off-diagonal influence and zero diagonal;
- [x] exact row sums and canonical coefficient;
- [x] minimality among admissible Dobrushin matrices;
- [x] normalized random-scan variation contraction;
- [x] centered spectral and Rayleigh consequences;
- [x] family-wide Hamiltonian and excitation consequences;
- [x] conditional transfer-orbit route.

The former roadmap item “Dobrushin TV to centered `L2` Rayleigh contraction” is complete. The remaining input is a physically relevant, scale-uniform proof of `alpha_can < 1`.

### 3. Exact plaquette-supported influence

PRs #273--#274 prove:

- [x] target-local / target-remote action decomposition;
- [x] cancellation of the remote factor in normalized conditionals;
- [x] zero conditional TV outside plaquette support;
- [x] zero canonical influence outside plaquette support;
- [x] active-neighbor profile with zero diagonal removed;
- [x] `alpha_can <= d_active * eta_active`;
- [x] sharp normalized-exponential TV comparison;
- [x] exact localization of source response to shared plaquettes;
- [x] the quantitative bound

```text
eta_active <=
  (exp (2 * beta * m_shared * E_max) - 1) /
  (exp (2 * beta * m_shared * E_max) + 1).
```

### 4. Periodic four-dimensional geometry

PRs #278 and #281--#286 construct the signed periodic hypercubic geometry.

For side length `n >= 3`, `main` proves:

- [x] active physical-link degree `d_active <= 18`;
- [x] shared-plaquette multiplicity `m_shared <= 1` for distinct active links.

The condition `n >= 3` is essential because side length two has a real periodic wrap-around degeneracy.

### 5. Orientation-correct Wilson foundation

PR #287 introduces `FiniteOrientedLatticeWilsonSystem`:

- [x] configurations live on physical positive links only;
- [x] forward/backward traversal is recorded per boundary incidence;
- [x] signed step gauge covariance;
- [x] plaquette-holonomy conjugation covariance;
- [x] gauge invariance of the oriented Wilson action;
- [x] physical neighbor and shared-plaquette finsets.

PR #288 adds the periodic four-dimensional `Z2` instance and an oriented incidence certificate with `d_active <= 18` and `m_shared <= 1`.

The older finite Wilson theorems remain valid for their declared model, but the physical quantitative lane should migrate to the oriented interface.

---

## Milestone 1 — complete orientation-correct locality

Status: **in progress in PR #289**

- [x] physical-link replacement;
- [x] agreement away from one replaced source link;
- [x] signed holonomy congruence;
- [x] non-neighbor plaquette invariance;
- [x] target-local / target-remote action decomposition;
- [ ] merge and replay PR #289;
- [ ] define the oriented Gibbs PMF and exact single-link conditional PMF;
- [ ] prove remote-factor cancellation under normalization;
- [ ] prove exact zero influence outside physical plaquette support;
- [ ] connect the oriented geometry to the canonical influence API.

Definition of done:

```text
The periodic oriented Wilson system produces exact conditional laws and
canonical influences using physical links only.
```

---

## Milestone 2 — close the periodic `Z2` quantitative theorem

- [ ] package the oriented `Z2` plaquette-energy maximum as `E_max = 1`;
- [ ] feed `d_active <= 18` and `m_shared <= 1` into the active profile;
- [ ] derive

```text
eta_active <= (exp (2 * beta) - 1) / (exp (2 * beta) + 1);
```

- [ ] derive a sufficient strict criterion `18 * eta_active < 1`;
- [ ] generate the centered-Rayleigh, finite Hamiltonian-gap, and excitation consequences;
- [ ] add explicit finite examples and compile smokes;
- [ ] state the exact parameter range.

This is an exact finite-volume theorem. The resulting single-link criterion is expected to be a restrictive small-`beta` condition and must not be presented as a continuum weak-coupling result.

---

## Milestone 3 — obtain a continuum-relevant uniform estimate

The intended continuum scaling may require more than single-link Dobrushin control.

Candidate routes:

- [ ] block dynamics or block-Dobrushin estimates;
- [ ] multiscale or polymer estimates;
- [ ] approximate tensorization on blocks;
- [ ] reflection-positive transfer estimates;
- [ ] another explicitly justified scale-uniform coercive mechanism.

Requirements:

- [ ] track lattice spacing, physical volume, coupling, gauge group, and boundary conditions;
- [ ] prove constants uniformly along a specified approximation family;
- [ ] avoid assuming the desired mass gap;
- [ ] connect the estimate to the canonical or physical transfer Hamiltonian.

---

## Milestone 4 — compact non-Abelian oriented Wilson theory

The present oriented interface uses a finite gauge group, and the concrete instance is `Z2`.

- [ ] define orientation-correct compact-group configuration spaces;
- [ ] replace finite sums by Haar integration and measurable kernels;
- [ ] construct exact regular conditional single-link laws;
- [ ] prove gauge covariance and invariance;
- [ ] define canonical influence or block influence;
- [ ] specialize to the intended compact non-Abelian group;
- [ ] prove a continuum-relevant quantitative estimate.

---

## Milestone 5 — physical weak limit

Open PR #282 implements the generic route:

```text
varying finite lattice laws
  -> measurable embeddings into one Polish carrier
  -> pushforward ProbabilityMeasures
  -> coercive moment
  -> compact containment
  -> tightness
  -> Prokhorov subsequence
  -> weak physical limit,
     with a_n -> 0 and V_n -> infinity.
```

Repository tasks:

- [ ] merge and integrate PR #282;
- [ ] choose a concrete gauge-compatible physical carrier;
- [ ] define interpolation or blocking maps;
- [ ] specify the renormalized coupling trajectory;
- [ ] construct a compact-sublevel coercive functional;
- [ ] prove the uniform Wilson moment estimate;
- [ ] prove nontriviality and interacting character;
- [ ] prove uniqueness or characterize phase selection;
- [ ] pass finite correlation estimates to the limit.

---

## Milestone 6 — physical transfer normalization

The algebraically rescaled finite Hamiltonian is not yet a physically normalized transfer Hamiltonian.

- [ ] construct the Euclidean time-slice transfer operator;
- [ ] identify its Hilbert space, vacuum, and centered sector;
- [ ] prove positivity and symmetry/self-adjointness;
- [ ] derive the relation to the heat-bath or block generator;
- [ ] track lattice spacing and physical units;
- [ ] prove the scale relation uniformly;
- [ ] do not import `exactGapValueReal` into the derivation.

---

## Milestone 7 — continuum clustering and reconstruction

- [ ] prove physical finite-volume correlation decay;
- [ ] prove uniform amplitude/readout bounds;
- [ ] pass decay to the continuum law;
- [ ] prove reflection positivity, Euclidean covariance, and regularity;
- [ ] prove clustering and nontriviality;
- [ ] reconstruct the physical Hilbert space and Hamiltonian;
- [ ] identify a positive physical spectral gap;
- [ ] obtain independent replay and specialist review.

---

## Exact `33/20` lane

Status: **internal normalization/audit carrier, not an independently derived physical value**

- [x] the value `33/20` is defined and transported through internal spectral/PVM and R6--R7 interfaces;
- [x] finite heat-bath and normalized layers are formally separated;
- [ ] derive the physical scale independently of `exactGapValueReal`;
- [ ] construct the continuum physical Hamiltonian independently;
- [ ] derive its spectral infimum and positive observable weight;
- [ ] prove, rather than preload, any equality with `33/20`;
- [ ] obtain external review of any exact-value claim.

## Release gates

### Source gate

- [ ] fresh-clone `lake build`;
- [ ] `bash scripts/check.sh`;
- [ ] every documentation claim has a source anchor;
- [ ] placeholder inventory is current;
- [ ] overtaken open PRs are closed or rebased;
- [ ] oriented files are included in standard replay coverage.

### Mathematical gate

- [ ] oriented conditional-law and influence spine;
- [ ] periodic `Z2` quantitative theorem;
- [ ] compact non-Abelian physical finite model;
- [ ] continuum-relevant uniform estimate;
- [ ] physical transfer normalization;
- [ ] concrete nontrivial continuum limit;
- [ ] OS/Wightman hypotheses discharged.

### External-claim gate

- [ ] independent replay;
- [ ] dependency and assumption audit;
- [ ] specialist review;
- [ ] no hidden use of the target mass gap or target numerical value;
- [ ] public wording matches the theorem boundary.

## Execution order

```text
PR #289 oriented locality
  -> oriented conditional law and influence
  -> periodic Z2 finite quantitative theorem
  -> continuum-relevant block or multiscale estimate
  -> compact non-Abelian finite model
  -> instantiate the PR #282 weak-limit framework
  -> physical transfer normalization
  -> continuum clustering and OS/Wightman reconstruction
  -> independent validation.
```
