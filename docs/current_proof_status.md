# Current proof status

**Updated:** 2026-06-17  
**Latest merged checkpoint:** PR #263  
**Later pull request:** none found at the time of this update

## Status

The current source tree contains a concrete finite Wilson Gibbs, heat-bath, orthogonal-projection, Gibbs-Hilbert, canonical Hamiltonian, family-wide centered-Rayleigh implication, and explicitly rescaled Dobrushin Hamiltonian lane:

```text
finite Wilson Gibbs law
  -> exact single-link conditional law
  -> Gibbs and conditional variances
  -> heat-bath Dirichlet form
  -> projection P_e
  -> fluctuation projection Q_e = I - P_e
  -> exact detailed balance and reversible product sums
  -> Gibbs symmetry and P_e/Q_e orthogonality
  -> Gibbs-weighted Pythagoras
  -> averaged local variance = Gibbs squared norm of Q_e
  -> concrete Gibbs Hilbert equivalence
  -> canonical H_HB = sum_e Q_e
  -> exact Hamiltonian/Dirichlet quadratic-form identity
  -> H_HB = |E| (I - P_scan)
  -> centered random-scan Rayleigh coercivity
  -> family-wide finite Poincare and Hamiltonian gap consequences
  -> explicitly Dobrushin-rescaled finite heat-bath Hamiltonian.
```

## Proved on `main`

The following formerly open steps are now proved:

- Gibbs-pairing symmetry of the exact single-link projection `P_e` and fluctuation projection `Q_e`;
- orthogonality of the projection and fluctuation ranges;
- the Gibbs-weighted Pythagorean decomposition;
- the exact identity
  `averagedSingleLinkVariance f e = gibbsPairingReal (Q_e f) (Q_e f)`;
- the full heat-bath Dirichlet form as the sum of local fluctuation squared norms;
- the finite Gibbs Hilbert carrier, normalized vacuum, and observable/Hilbert linear equivalence;
- the centered Hilbert norm/Gibbs-variance identity for every Hilbert vector;
- the canonical observable heat-bath Hamiltonian `sum_e Q_e`;
- symmetry, zero vacuum energy, and the exact Dirichlet quadratic-form identity;
- the exact generator/random-scan relation
  `H_HB = |E| (I - P_scan)`;
- the exact link-count-scaled random-scan Rayleigh-defect identity;
- centered Rayleigh contraction implies the correctly scaled finite heat-bath Poincare inequality;
- the canonical finite Hamiltonian coercivity and excitation-sector lower-bound route;
- the family-wide package merged in PR #262, which derives these consequences at every approximation index from a family of centered-Rayleigh certificates;
- the PR #263 Dobrushin-scaled lane, conditional on a
  `FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate`, including:
  - `(1 - alpha) * Var_mu(f) <= E_HB(f)`;
  - the explicitly scaled symmetric Gibbs-Hilbert Hamiltonian;
  - zero vacuum energy and the scaled quadratic-form identity;
  - the `exactGapValueReal` lower bound on the finite vacuum-orthogonal sector;
  - the corresponding excitation-eigenvalue lower bound.

The gap consequences remain conditional: neither PR #262 nor PR #263 derives the centered-Rayleigh estimate from the Wilson action or from the Dobrushin matrix alone.

## Dobrushin and normalization status

PR #261 defines

```text
alpha      = Dobrushin coefficient,
lambda_HB  = 1 - alpha,
rho_scan   = 1 - (1 - alpha) / |E|,
```

and proves, for a nonempty edge set,

```text
0 <= rho_scan < 1,
|E| (1 - rho_scan) = lambda_HB.
```

The old unscaled random-scan certificates required a Markov contraction gap bounded by one to dominate `exactGapValueReal > 1`. PR #255 proves those old system-level and family-level structures uninhabited. The impossible route is therefore explicitly closed.

The replacement lane separates the heat-bath gap from the normalized carrier. PR #261 defines

```text
scale_HB = exactGapValueReal / lambda_HB
```

and proves

```text
scale_HB * lambda_HB = exactGapValueReal.
```

PR #263 transports this algebraic scale to a finite symmetric Gibbs-Hilbert Hamiltonian and its vacuum-orthogonal lower bound.

This is **not** a physical derivation of the normalization scale: the numerator is the pre-existing normalized carrier. A transfer-time or generator normalization derived independently from Wilson dynamics remains open.

## Principal remaining finite-volume analytic input

The finite Dobrushin matrix controls one-link conditional laws in total variation. The canonical and scaled Hamiltonian lanes require the centered Gibbs-pairing estimate

```text
<P_scan f, f>_mu <= rho_scan <f, f>_mu,
E_mu[f] = 0.
```

The repository represents this as a separate
`FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate`. The implication

```text
Dobrushin TV row-sum bound
  -> centered Gibbs L2/Rayleigh contraction
```

has not yet been proved. Actual Wilson influence coefficients and a volume- and lattice-spacing-uniform bound also remain open.

## Exact `33/20` dependency

The numerical value enters in

```text
MGAP4D/MathlibAnalytic/HamiltonianPVMSpectralExactGapValue.lean
```

through

```lean
hamiltonianPVMSpectralNormalized3320Value := (33 : Real) / 20.
```

`ExactGapReal.lean` projects `exactGapValueReal` from that package. Later spectral, R6, and R7 files transport the same value. The explicit Dobrushin scale uses `exactGapValueReal` as its numerator. None of these facts independently derives `33/20` from a physical Yang--Mills Hamiltonian.

## Claim table

| Claim | Status |
|---|---|
| Exact finite Wilson conditional law | constructed |
| Gibbs variance and heat-bath Dirichlet form | constructed |
| Algebraic `P_e` and `Q_e` projections | constructed |
| Detailed balance and reversible product sum | proved |
| Gibbs symmetry and orthogonality | proved on `main` |
| Weighted Pythagoras and local fluctuation norm | proved on `main` |
| Concrete finite Gibbs Hilbert realization | constructed on `main` |
| Canonical finite heat-bath Hamiltonian | constructed on `main` |
| Hamiltonian/Dirichlet quadratic form | proved on `main` |
| `H_HB = |E|(I-P_scan)` | proved on `main` |
| Centered Rayleigh certificate -> finite Poincare/Hamiltonian gap | proved on `main` |
| Family-wide centered-Rayleigh gap package | proved on `main` via PR #262 |
| Dobrushin heat-bath/random-scan rate identities | proved on `main` |
| Dobrushin-scaled finite Hamiltonian | constructed conditionally on `main` via PR #263 |
| Dobrushin TV -> centered `L²` Rayleigh contraction | open |
| Uniform Wilson influence estimate | open |
| Physical derivation of the normalization scale | open |
| Physical transfer Hamiltonian identification | open |
| Continuum clustering | conditional |
| Nontrivial continuum Yang--Mills measure | open |
| Physical mass gap | open |
| Independent physical derivation of `33/20` | open |
| External consensus | not claimed |

## Next steps

1. Derive centered Gibbs `L²`/Rayleigh contraction from the Dobrushin influence package.
2. Construct actual Wilson influence coefficients and prove a scale-uniform row-sum or block estimate.
3. Derive the physical transfer-time/generator normalization independently of `exactGapValueReal`.
4. Prove uniform transfer contraction, nontrivial continuum convergence, and the analytic OS/Wightman hypotheses.
5. Obtain independent replay, dependency review, and expert validation.

Lean theorem bodies are authoritative. Conditional structures, algebraically defined normalization scales, and internal exact-gap carriers must not be presented as unconditional physical results.