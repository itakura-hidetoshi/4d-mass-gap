# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / Lake repository for a proof-carrying investigation of the four-dimensional Yang--Mills mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Current status — 2026-06-17

The current `main` branch is a **replayable formal-development and internal review surface**. It is not a completed public solution of the four-dimensional Yang--Mills existence and mass-gap problem.

The latest merged checkpoint is PR **#263**. The finite Wilson lane now contains:

```text
exact single-link Wilson heat bath
  -> Gibbs-symmetric orthogonal projections P_e and Q_e
  -> concrete Gibbs Hilbert realization
  -> canonical H_HB = sum_e Q_e
  -> exact Dirichlet quadratic form
  -> H_HB = |E| (I - P_scan)
  -> centered random-scan Rayleigh certificate
  -> family-wide finite Poincare and Hamiltonian gap consequences
  -> explicitly Dobrushin-rescaled finite heat-bath Hamiltonian.
```

No later pull request was found at the time of this update.

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
  -> Gibbs-weighted Pythagorean decomposition
  -> E_mu[Var_e(f)] = <Q_e f, Q_e f>_mu
  -> concrete Gibbs Hilbert equivalence
  -> H_HB = sum_e Q_e
  -> <H_HB x, x> = heat-bath Dirichlet energy
  -> H_HB = |E| (I - P_scan).
```

The following are on `main`:

- finite Gibbs expectation, variance, and exact single-link conditional laws;
- the global single-link heat-bath Dirichlet form;
- idempotent `P_e` and complementary `Q_e`;
- exact detailed balance and reversible finite product sums;
- Gibbs-pairing symmetry of `P_e` and `Q_e`;
- Gibbs orthogonality of their ranges;
- the Gibbs-weighted Pythagorean identity;
- the exact averaged local-variance/fluctuation-norm identity;
- the full Dirichlet form as the sum of local Gibbs squared norms;
- the finite Gibbs Hilbert carrier, normalized vacuum, and observable/Hilbert linear equivalence;
- the canonical observable and Gibbs-Hilbert heat-bath Hamiltonians;
- Hamiltonian symmetry, zero vacuum energy, and the exact quadratic-form identity;
- the normalized random-scan operator and exact link-count scaling relation.

The local projection, weighted-Hilbert, and finite heat-bath Hamiltonian construction obligations are therefore closed on `main`.

### 2. Random-scan Rayleigh and Dobrushin lane

The canonical generator and normalized random scan satisfy

```text
H_HB = |E| (I - P_scan).
```

A centered Gibbs-pairing Rayleigh estimate

```text
<P_scan f, f>_mu <= rho <f, f>_mu,
E_mu[f] = 0,
```

yields the correctly scaled heat-bath coercivity constant

```text
lambda_HB = |E| (1 - rho).
```

This conversion is proved on `main`, including:

- the exact Rayleigh-defect identity;
- finite heat-bath Poincare coercivity;
- the canonical finite Hamiltonian lower bound;
- vacuum-orthogonal and excitation-eigenvalue consequences;
- the family-wide lift merged in PR #262.

From finite Dobrushin matrix data, PR #261 defines

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

PR #263 additionally proves, conditional on a
`FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate`, the unnormalized coercive estimate

```text
(1 - alpha) Var_mu(f) <= E_HB(f),
```

rescales the canonical finite heat-bath Hamiltonian by

```text
scale_HB = exactGapValueReal / (1 - alpha),
```

and derives the corresponding `exactGapValueReal` lower bound on the finite vacuum-orthogonal and excitation sectors.

The source deliberately keeps the following as a separate certificate:

```text
Dobrushin TV row-sum control
  -> centered Gibbs L2/Rayleigh contraction of P_scan.
```

That theorem has **not** yet been derived from the matrix package. Actual Wilson influence coefficients and a volume- and lattice-spacing-uniform bound also remain open.

### 3. Conditional transfer and continuum lane

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

The finite Gibbs-Hilbert heat-bath Hamiltonian is constructed rather than postulated. The remaining physical task is to identify its correctly scaled generator with the physical transfer Hamiltonian across the approximation family and continuum limit.

Still open:

- Dobrushin influence data to centered `L²`/Rayleigh contraction;
- concrete scale-uniform Wilson influence or block-dynamics estimates;
- a physically derived transfer-time or generator normalization;
- a uniform transfer-orbit amplitude estimate;
- convergence to a nontrivial regular continuum Yang--Mills measure;
- discharge of the analytic OS/Wightman hypotheses;
- independent validation of the physical mass-gap conclusion.

### 4. Normalized exact-gap audit lane

The source tree carries a normalized value `33/20` through internal Hamiltonian/PVM/spectral and R6--R7 audit interfaces. This is a typed normalization and dependency-routing surface, but it is **not an independent derivation of the physical four-dimensional Yang--Mills mass gap**.

```text
HamiltonianPVMSpectralExactGapValue.lean
  defines hamiltonianPVMSpectralNormalized3320Value := 33/20

ExactGapReal.lean
  projects exactGapValueReal from that package

later spectral / R6 / R7 files
  transport and audit the same carried value.
```

Read `docs/exact_gap_layer_separation.md` for the dependency-level account.

## Normalization status

The former unscaled random-scan route required a Markov contraction gap bounded by one to dominate `exactGapValueReal > 1`. PR #255 proves the affected old certificate structures uninhabited, so that inconsistent route is explicitly closed.

The replacement lane separates:

```text
lambda_HB        = heat-bath coercivity gap,
rho_scan         = normalized random-scan rate,
scale_HB > 0     = conversion to the normalized carrier,
Delta_norm       = scale_HB * lambda_HB.
```

PR #261 defines

```text
scale_HB = exactGapValueReal / lambda_HB
```

and proves the resulting algebraic equality. PR #263 transports this algebraic rescaling to a symmetric finite Gibbs-Hilbert Hamiltonian, proves zero vacuum energy and its scaled quadratic form, and derives the normalized lower bound conditional on the centered-Rayleigh certificate.

This is mathematically valid as an algebraic rescaling, but it does **not** derive the scale from Wilson dynamics or transfer time: the numerator remains the pre-existing normalized carrier. A physical normalization theorem remains open.

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
| Centered Rayleigh certificate -> finite gap | Proved for one system and family-wide on `main` |
| Dobrushin rate normalization | `1-alpha`, `1-(1-alpha)/|E|`, positivity, and link-count identity are proved |
| Dobrushin-scaled finite Hamiltonian | Constructed conditionally on the centered-Rayleigh certificate |
| Dobrushin TV -> centered `L²` Rayleigh contraction | Not yet proved |
| Uniform Wilson influence estimate | Not proved |
| Physical heat-bath -> transfer scale | Not dynamically derived |
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
| Family-wide Rayleigh gap | `MGAP4D/MathlibAnalytic/FiniteWilsonRandomScanRayleighFamilyGap.lean` |
| Dobrushin scale separation | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonDobrushinRandomScanScale.lean` |
| Dobrushin-scaled Hamiltonian | `MGAP4D/MathlibAnalytic/FiniteWilsonDobrushinScaledHamiltonianGap.lean` |
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

1. Derive centered Gibbs `L²`/Rayleigh contraction from the finite Dobrushin influence package.
2. Construct actual Wilson influence coefficients and prove a scale-uniform bound, or justify a block-dynamics replacement.
3. Derive the physical transfer-time/generator scale independently of `exactGapValueReal`.
4. Prove uniform transfer contraction, nontrivial continuum convergence, and the analytic OS/Wightman hypotheses.
5. Subject the complete dependency chain and physical interpretation to independent review.

## Public claim boundary

Recommended wording:

```text
MGAP4D is a Lean 4 formal-development repository for a four-dimensional
Yang--Mills mass-gap proof architecture. It contains a concrete finite Wilson
heat-bath probability lane, orthogonal projection and Gibbs-Hilbert
realizations, a constructed canonical finite heat-bath Hamiltonian, exact
random-scan scaling identities, family-wide conditional finite-gap theorems,
and an explicitly rescaled finite Dobrushin Hamiltonian. The Dobrushin-to-L2
theorem, scale-uniform Wilson estimate, physical normalization and transfer
identification, nontrivial continuum construction, and independent derivation
of the physical mass gap remain open.
```