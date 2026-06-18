# Current proof status

**Updated:** 2026-06-18  
**Latest merged checkpoint:** PR #288  
**Latest merged commit:** `59c5780e1efd9e0035aad9bb8c65ff752f5b89dc`  
**Active proof PRs:** #289 and #282

## Status

The repository is a replayable finite-volume and continuum-architecture development. It does **not** yet prove an unconditional four-dimensional Yang--Mills continuum theory or physical mass gap.

The merged chain now includes:

```text
finite Wilson Gibbs law
  -> exact single-link conditional law
  -> P_e and Q_e projections
  -> Gibbs Hilbert realization
  -> canonical H_HB = sum_e Q_e
  -> H_HB = |E| (I - P_scan)
  -> exact canonical conditional-TV influence
  -> Dobrushin variation contraction
  -> centered spectral/Rayleigh contraction
  -> finite Hamiltonian gap consequences
  -> exact plaquette-supported influence bounds
  -> periodic 4D incidence bounds
  -> orientation-correct periodic Z2 Wilson foundation.
```

The previous status document stopped at PR #263. Its statement that Dobrushin conditional-TV control had not yet been converted to centered Gibbs `L2`/Rayleigh contraction is obsolete: PR #272 proves that finite abstract route.

## Proved on `main`

### Finite Gibbs, projection, and Hamiltonian structure

- exact finite Wilson Gibbs and single-link conditional PMFs;
- Gibbs expectation, variance, and heat-bath Dirichlet form;
- conditional-expectation projection `P_e` and fluctuation projection `Q_e`;
- detailed balance, symmetry, orthogonality, and weighted Pythagoras;
- concrete finite Gibbs Hilbert realization and normalized vacuum;
- canonical finite heat-bath Hamiltonian;
- zero vacuum energy and exact quadratic-form identity;
- exact relation `H_HB = |E| (I - P_scan)`.

### Canonical Dobrushin-to-Rayleigh route

PRs #267--#272 prove:

- exact off-diagonal conditional-TV influences and zero diagonal;
- exact row sums and canonical coefficient `alpha_can`;
- minimality among admissible Dobrushin matrices;
- link-variation and total-variation seminorms;
- one-update and normalized random-scan contraction;
- iterate contraction and centered fixed-point triviality;
- nonconstant eigenvalue control;
- symmetric Gibbs-Hilbert spectral lift;
- centered random-scan Rayleigh contraction;
- automatic finite Hamiltonian and excitation lower bounds from `alpha_can < 1`.

Thus the remaining finite quantitative input is a physically relevant proof of `alpha_can < 1`, not a separate Rayleigh certificate.

### Exact plaquette-supported influence

PRs #273--#274 prove:

- target-local / target-remote action decomposition;
- cancellation of the remote factor in normalized conditionals;
- exact zero influence outside plaquette support;
- active neighbors with the zero diagonal removed;
- `alpha_can <= d_active * eta_active`;
- sharp normalized-exponential total-variation comparison;
- exact shared-plaquette localization;
- the bound

```text
eta_active <=
  (exp (2 * beta * m_shared * E_max) - 1) /
  (exp (2 * beta * m_shared * E_max) + 1).
```

### Periodic four-dimensional geometry

PRs #278 and #281--#286 prove, for side length `n >= 3`:

```text
d_active <= 18,
m_shared <= 1.
```

The restriction `n >= 3` is essential because side length two has a periodic shared-plaquette degeneracy.

### Orientation-correct Wilson foundation

PR #287 introduces `FiniteOrientedLatticeWilsonSystem`, with one variable per physical positive link and a separate forward/backward orientation on each plaquette boundary incidence. It proves signed gauge covariance, plaquette-holonomy conjugation covariance, action gauge invariance, and physical incidence finsets.

PR #288 instantiates the periodic four-dimensional `Z2` system and packages `d_active <= 18` and `m_shared <= 1` into an oriented incidence certificate.

The legacy finite Wilson spine remains valid for its declared interface, but it has not yet been fully transported to the orientation-correct system.

## Active pull requests

### PR #289 — orientation-correct locality

State: **open and mergeable**.

It adds physical-link replacement, agreement away from one source link, signed holonomy congruence, non-neighbor locality, and target-local/target-remote action decomposition. This is the foundation for an oriented exact conditional-law and influence lane. It is not yet on `main`.

### PR #282 — physical weak limits

State: **open and mergeable**.

It adds varying lattice configuration types embedded into one fixed Polish carrier, pushforward `ProbabilityMeasure`s, weak convergence, bounded-continuous observable convergence, symmetry inheritance, compact containment, tightness, coercive moments, and Prokhorov subsequence extraction while preserving `a_n -> 0` and `V_n -> infinity`.

The concrete analytic inputs remain open: the physical carrier, interpolation maps, renormalized trajectory, compact-sublevel functional, uniform Wilson moment estimate, nontriviality, uniqueness or phase selection, reflection positivity, Euclidean covariance, clustering, and regularity.

## Present frontier

For the periodic oriented `Z2` system, the merged geometry gives

```text
d_active <= 18,
m_shared <= 1,
plaquette energy in {0,1}.
```

The next finite theorem is to connect the oriented conditional law to the merged quantitative interface, package `E_max = 1`, and derive

```text
eta_active <= (exp (2 * beta) - 1) / (exp (2 * beta) + 1),
18 * eta_active < 1
  -> alpha_can < 1
  -> centered Rayleigh contraction
  -> finite Hamiltonian gap.
```

This would be an exact finite-volume result. The single-link condition is expected to be a restrictive small-`beta` regime and is not by itself a continuum weak-coupling theorem. A block or multiscale replacement may be required.

## Claim table

| Claim | Status |
|---|---|
| Finite Gibbs/projection/Hilbert/Hamiltonian spine | proved or constructed on `main` |
| Exact canonical Dobrushin matrix | constructed on `main` |
| Strict canonical coefficient -> centered Rayleigh contraction | proved on `main` via PR #272 |
| Exact plaquette support and shared-plaquette majorant | proved on `main` via PR #274 |
| Periodic 4D bounds `d_active <= 18`, `m_shared <= 1` | proved on `main` for `n >= 3` |
| Orientation-correct finite Wilson system and periodic `Z2` instance | constructed on `main` |
| Orientation-correct locality bridge | open in PR #289 |
| Oriented conditional/Dobrushin/Hamiltonian spine | incomplete |
| Explicit periodic `Z2` strict-coefficient theorem | open |
| Continuum-relevant uniform estimate | open |
| Compact non-Abelian oriented finite theory | open |
| Physical weak-limit framework | implemented in open PR #282 |
| Concrete nontrivial continuum Yang--Mills measure | open |
| Physical transfer normalization | open |
| OS/Wightman analytic hypotheses | open |
| Physical mass gap | open |
| Independent physical derivation of `33/20` | open |
| External consensus | not claimed |

## Exact `33/20` dependency

`HamiltonianPVMSpectralExactGapValue.lean` defines the normalized value `33/20`; `ExactGapReal.lean` projects `exactGapValueReal`, and later audit files transport the same value. This is an internal normalization and dependency-routing lane, not an independent physical derivation.

## Next steps

1. Merge and replay PR #289.
2. Construct the oriented Gibbs PMF, exact conditional law, and canonical influence.
3. Package `E_max = 1` and derive the periodic `Z2` finite strict-coefficient theorem.
4. Develop a block, multiscale, or other continuum-relevant uniform estimate if single-link Dobrushin is insufficient.
5. Extend to the intended compact non-Abelian gauge group.
6. Merge and instantiate PR #282 with concrete uniform estimates.
7. Derive physical transfer normalization independently of `exactGapValueReal`.
8. Prove nontrivial continuum convergence, clustering, OS/Wightman reconstruction, and obtain independent review.

Lean theorem bodies are authoritative. Open-PR results, conditional assumptions, algebraically selected scales, and internal exact-gap carriers must not be presented as unconditional physical conclusions.
