# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / Lake repository for a proof-carrying investigation of the four-dimensional Yang--Mills mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Current status — 2026-06-17

The current `main` branch is a **replayable formal-development and internal review surface**. It is not a completed public solution of the four-dimensional Yang--Mills existence and mass-gap problem.

The latest merged checkpoint is PR **#261**. The finite Wilson lane now includes Gibbs-pairing symmetry and orthogonality of the exact single-link heat-bath projections, a concrete finite Gibbs Hilbert realization, the canonical finite heat-bath Hamiltonian

```text
H_HB = sum_e Q_e,
```

its exact Dirichlet quadratic-form identity, the correctly normalized random-scan identity

```text
H_HB = |E| (I - P_scan),
```

and a separated Dobrushin heat-bath gap / normalized-gap scale interface. PR **#262** is the active open continuation and lifts centered random-scan Rayleigh certificates to an approximation family; it is not yet part of `main`.

## Proof lanes

The source tree contains four related lanes that must not be conflated.

### 1. Concrete finite Wilson heat-bath and Hilbert lane

This lane is built from actual finite Wilson Gibbs weights and exact single-link conditional laws.

```text
finite Wilson action and Gibbs PMF
  -> exact single-link conditional PMF
  -> Gibbs expectation and variance
  -> conditional expectation and variance
  -> single-link heat-bath Dirichlet form
  -> projection P_e
  -> fluctuation projection Q_e = I - P_e
  -> exact detailed balance and reversible product sums
  -> Gibbs symmetry and P_e/Q_e orthogonality
  -> Pythagorean decomposition
  -> E_mu[Var_e(f)] = <Q_e f, Q_e f>_mu
  -> concrete Gibbs Hilbert equivalence
  -> H_HB = sum_e Q_e
  -> <H_HB x, x> = heat-bath Dirichlet energy
  -> H_HB = |E| (I - P_scan)
```

The following components are on `main`:

- finite Gibbs expectation, variance, exact single-link conditional PMFs, expectations, and variances;
- the global single-link heat-bath Dirichlet form;
- the idempotent conditional-expectation projection `P_e` and complementary projection `Q_e`;
- exact detailed balance and the reversible finite product-sum theorem;
- Gibbs-pairing symmetry of `P_e` and `Q_e`;
- Gibbs orthogonality of the projection and fluctuation ranges;
- the Gibbs-weighted Pythagorean identity;
- the exact averaged local-variance identity
  `averagedSingleLinkVariance f e = gibbsPairingReal (Q_e f) (Q_e f)`;
- the full Dirichlet form as the sum of the Gibbs squared norms of the local fluctuations;
- the finite Gibbs Hilbert carrier obtained by multiplication by `sqrt(mu)` and its inverse linear equivalence;
- the normalized vacuum vector and the centered-norm/Gibbs-variance theorem;
- the canonical observable and Gibbs-Hilbert heat-bath Hamiltonians;
- symmetry, zero vacuum energy, and the exact Hamiltonian quadratic-form identity;
- the normalized random-scan operator and the exact link-count scaling relation.

Thus the earlier local operator obligations—Gibbs symmetry, orthogonality, Pythagoras, fluctuation norm, finite Hilbert realization, and the finite heat-bath Hamiltonian construction—are no longer open on `main`.

### 2. Random-scan Rayleigh and Dobrushin lane

The canonical generator and the normalized random scan satisfy the exact finite identity

```text
H_HB = |E| (I - P_scan).
```

Consequently, a centered Gibbs-pairing Rayleigh estimate

```text
<P_scan f, f>_mu <= rho <f, f>_mu,
E_mu[f] = 0,
```

yields the correctly scaled coercivity constant

```text
lambda_HB = |E| (1 - rho).
```

This implication is proved on `main`, including the conversion to the exact heat-bath Poincare interface and then to the canonical finite Hamiltonian lower bound.

PR #261 also defines, from finite Dobrushin matrix data,

```text
alpha      = Dobrushin coefficient,
lambda_HB  = 1 - alpha,
rho_scan   = 1 - (1 - alpha) / |E|,
```

and proves

```text
0 <= rho_scan < 1,
|E| (1 - rho_scan) = lambda_HB.
```

However, the source deliberately keeps the following as a separate certificate:

```text
Dobrushin TV row-sum control
  -> centered Gibbs L2/Rayleigh contraction of P_scan.
```

That theorem has **not** yet been derived from the matrix package. The actual Wilson influence coefficients and a volume- and lattice-spacing-uniform bound also remain open.

### 3. Conditional Hamiltonian, transfer, and continuum lane

The repository contains typed implication chains of the form

```text
uniform finite-volume centered Rayleigh/coercivity input
  -> canonical finite heat-bath Hamiltonian gap
  -> transfer contraction
  -> finite-volume correlation decay
  -> continuum clustering
  -> OS/Wightman assembly
  -> projective-limit continuum routes.
```

The finite Gibbs-Hilbert heat-bath Hamiltonian is now constructed rather than postulated. The remaining physical step is not that finite construction, but the identification of the correctly scaled heat-bath generator with the physical transfer Hamiltonian across the approximation family and continuum limit.

The following remain open:

- a proved centered `L²`/Rayleigh contraction theorem from the Dobrushin influence package;
- concrete Wilson influence coefficients with a scale-uniform quantitative bound;
- a physically derived transfer-time or generator normalization;
- a uniform transfer-orbit amplitude estimate;
- convergence to a nontrivial regular continuum Yang--Mills measure;
- discharge of the analytic OS/Wightman reconstruction hypotheses;
- independent mathematical validation of the physical mass-gap conclusion.

### 4. Normalized exact-gap audit lane

The source tree carries a normalized value `33/20` through internal Hamiltonian/PVM/spectral and R6--R7 audit interfaces. This is a useful typed normalization and dependency-routing surface, but it is **not an independent derivation of the physical four-dimensional Yang--Mills mass gap**.

```text
HamiltonianPVMSpectralExactGapValue.lean
  defines hamiltonianPVMSpectralNormalized3320Value := 33/20
  and constructs an internal certified package carrying that normalization

ExactGapReal.lean
  projects exactGapValueReal from that package

later spectral / R6 / R7 files
  align, transport, and audit the same carried value.
```

Read `docs/exact_gap_layer_separation.md` for the dependency-level account.

## Normalization status

The former unscaled random-scan route required a Markov contraction gap bounded by one to dominate `exactGapValueReal > 1`. PR #255 proves the affected old sweep and random-scan certificate structures uninhabited, so that inconsistent route is no longer presented as constructible.

The replacement lane now separates:

```text
lambda_HB        = heat-bath coercivity gap,
rho_scan         = normalized random-scan rate,
scale_HB > 0     = conversion to the normalized carrier,
Delta_norm       = scale_HB * lambda_HB.
```

PR #261 supplies an explicit positive scale

```text
scale_HB = exactGapValueReal / lambda_HB
```

and proves the resulting algebraic equality. This repairs the formal layer mismatch, but it does **not** derive the scale from Wilson dynamics or transfer time: the numerator is still the pre-existing normalized carrier. A physical normalization theorem remains open.

## What the repository currently proves

| Surface | Current reading |
|---|---|
| Finite Wilson Gibbs and conditional laws | Concrete definitions and finite identities are present |
| `P_e` and `Q_e` algebra | Idempotence, symmetry, orthogonality, decomposition, and weighted Pythagoras are proved |
| Detailed balance | Pointwise and finite product-sum reversibility are proved |
| Local variance / fluctuation norm | Exact Gibbs-weighted identity is proved |
| Finite Gibbs Hilbert realization | Constructed with an explicit linear equivalence and normalized vacuum |
| Canonical finite heat-bath Hamiltonian | Constructed; symmetric; zero vacuum energy; exact Dirichlet quadratic form |
| Random-scan/generator scaling | `H_HB = |E|(I-P_scan)` and the Rayleigh-defect identity are proved |
| Centered Rayleigh contraction -> finite gap | Proved as a conditional theorem |
| Dobrushin rate normalization | `1-alpha`, `1-(1-alpha)/|E|`, positivity, and link-count identity are proved |
| Dobrushin TV -> centered `L²` Rayleigh contraction | Not yet proved |
| Uniform Wilson influence estimate | Not proved |
| Heat-bath -> normalized physical scale | Algebraically separated; physical/dynamical derivation not proved |
| Transfer / continuum propagation | Typed conditional implication route is present |
| Nontrivial physical continuum construction | Not proved unconditionally |
| Physical derivation of `33/20` | Not established |
| External mathematical consensus | Not claimed |

## Primary review anchors

| Topic | File |
|---|---|
| Short status anchor | `docs/current_proof_status.md` |
| Development roadmap | `ROADMAP.md` |
| Exact-gap dependency separation | `docs/exact_gap_layer_separation.md` |
| Projection symmetry | `MGAP4D/MathlibAnalytic/FiniteWilsonHeatBathPairingSymmetry.lean` |
| Projection orthogonality | `MGAP4D/MathlibAnalytic/FiniteWilsonHeatBathPairingOrthogonality.lean` |
| Weighted Pythagoras | `MGAP4D/MathlibAnalytic/FiniteWilsonHeatBathPythagorean.lean` |
| Weighted fluctuation norm | `MGAP4D/MathlibAnalytic/FiniteWilsonHeatBathWeightedFluctuationNorm.lean` |
| Gibbs Hilbert realization | `MGAP4D/MathlibAnalytic/FiniteWilsonGibbsHilbertRealization.lean` |
| Gibbs Hilbert equivalence | `MGAP4D/MathlibAnalytic/FiniteWilsonGibbsHilbertEquivalence.lean` |
| Canonical heat-bath Hamiltonian | `MGAP4D/MathlibAnalytic/FiniteWilsonCanonicalHeatBathHamiltonian.lean` |
| Random-scan Rayleigh bridge | `MGAP4D/MathlibAnalytic/FiniteWilsonRandomScanRayleighContraction.lean` |
| Canonical Hamiltonian gap composition | `MGAP4D/MathlibAnalytic/FiniteWilsonRandomScanRayleighCanonicalHamiltonianGap.lean` |
| Dobrushin scale separation | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonDobrushinRandomScanScale.lean` |
| Continuum clustering route | `MGAP4D/MathlibAnalytic/FiniteWilsonOSAutomaticExactGapSingleLinkHeatBathTransferOrbitContraction.lean` |
| Full OS assembly route | `MGAP4D/MathlibAnalytic/FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitAssembly.lean` |
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

1. Complete the family-level centered random-scan Rayleigh lift represented by PR #262.
2. Derive centered Gibbs `L²`/Rayleigh contraction from the finite Dobrushin influence package.
3. Construct actual Wilson influence coefficients and prove a scale-uniform bound, or replace single-link Dobrushin by a justified block method.
4. Derive the physical transfer-time/generator scale rather than defining it from `exactGapValueReal`.
5. Prove uniform transfer contraction, nontrivial continuum convergence, and the analytic OS/Wightman hypotheses.
6. Subject the full dependency chain and physical interpretation to independent review.

## Public claim boundary

Recommended wording:

```text
MGAP4D is a Lean 4 formal-development repository for a four-dimensional
Yang--Mills mass-gap proof architecture. It contains a concrete finite Wilson
heat-bath probability lane, orthogonal projection and Gibbs-Hilbert
realizations, a constructed canonical finite heat-bath Hamiltonian, exact
random-scan scaling identities, and conditional routes from centered Rayleigh
coercivity to Hamiltonian and continuum statements. The Dobrushin-to-L2
estimate, scale-uniform Wilson bound, physical normalization and transfer
identification, nontrivial continuum construction, and independent derivation
of the physical mass gap remain open.
```