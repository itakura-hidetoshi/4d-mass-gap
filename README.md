# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / Lake repository for a proof-carrying investigation of the four-dimensional Yang--Mills mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Current status — 2026-06-17

The current `main` branch is a **replayable formal-development and internal review surface**. It is not a completed public solution of the four-dimensional Yang--Mills existence and mass-gap problem.

The latest merged finite Wilson checkpoint is PR **#241**, which proves the reversible product-sum identity for the exact single-link heat-bath transition. PR **#242** is open and is intended to derive symmetry of the single-link projection for the Gibbs pairing; it is not yet part of `main`.

The repository now contains three distinct lanes that must not be conflated.

### 1. Concrete finite Wilson heat-bath lane

This lane is built from actual finite Wilson Gibbs weights and exact single-link conditional laws.

```text
finite Wilson action and Gibbs PMF
  -> exact single-link conditional PMF
  -> Gibbs expectation and variance
  -> conditional expectation and conditional variance
  -> single-link heat-bath Dirichlet form
  -> idempotent projection P_e
  -> fluctuation projection Q_e = I - P_e
  -> local variance = fluctuation energy
  -> exact detailed balance
  -> finite transition reindexing
  -> reversible product-sum identity
```

The following components are already on `main`:

- finite Gibbs expectation and variance;
- exact single-link conditional PMFs, expectations, and variances;
- the global heat-bath Dirichlet form;
- off-link fiber invariance;
- the idempotent conditional-expectation projection `P_e`;
- its real-linear form and image/fixed-point characterization;
- the complementary fluctuation projection `Q_e = I - P_e`;
- conditional variance and Dirichlet energy expressed through `Q_e`;
- the concrete random-scan heat-bath sweep;
- conditional total variation and finite/uniform Dobrushin data interfaces;
- exact single-link detailed balance;
- the reversible finite product-sum theorem
  `finite_lattice_singleLinkHeatBath_reversible_product_sum`.

The next local operator step is Gibbs-pairing symmetry of `P_e`, followed by orthogonality of `P_e` and `Q_e` and the global weighted identity

```text
E_mu[Var_e(f)] = ||Q_e f||^2_{L^2(mu)}.
```

### 2. Conditional propagation lane

The repository also contains typed implication chains of the form

```text
uniform finite-volume coercivity / Poincare input
  -> vacuum Hamiltonian lower bound
  -> transfer contraction
  -> finite-volume correlation decay
  -> continuum clustering
  -> OS/Wightman assembly
  -> projective-limit continuum routes
```

These transformations are formalized, but their principal analytic inputs are not yet constructed unconditionally for the physical non-Abelian four-dimensional Wilson theory. In particular, the following remain open:

- a volume- and lattice-spacing-uniform quantitative estimate for the actual Wilson conditional laws;
- an operator theorem deriving the required random-scan contraction from the Dobrushin matrix package;
- a concrete Hilbert/observable realization and quadratic-form identity for the physical transfer Hamiltonian;
- a transfer-orbit representation with a uniform amplitude bound;
- convergence to a nontrivial regular continuum Yang--Mills measure;
- external validation of the OS/Wightman reconstruction and physical mass-gap conclusion.

### 3. Normalized exact-gap audit lane

The source tree carries a normalized value `33/20` through the internal Hamiltonian/PVM/spectral and R6--R7 audit interfaces. This is a useful typed normalization and dependency-routing surface, but it is **not yet an independent derivation of the physical four-dimensional Yang--Mills mass gap**.

The semantic origin is important:

```text
HamiltonianPVMSpectralExactGapValue.lean
  defines hamiltonianPVMSpectralNormalized3320Value := 33/20
  and constructs an internal certified package carrying that normalization

ExactGapReal.lean
  projects exactGapValueReal from that package

later spectral / R6 / R7 files
  align, transport, and audit the same carried value
```

Therefore, the absence of a literal `33/20` in `ExactGapReal.lean` is only a local syntactic separation. It does not by itself show that `33/20` was derived from a separately constructed physical Yang--Mills Hamiltonian.

Read `docs/exact_gap_layer_separation.md` for the full dependency-level account.

## Critical normalization issue

The current random-scan contraction interface includes

```text
0 <= rho < 1
exactGapValueReal <= 1 - rho.
```

At the same time, `exactGapValueReal_above_one` proves

```text
1 < exactGapValueReal.
```

Since `0 <= rho` implies `1 - rho <= 1`, these conditions cannot hold simultaneously. Consequently, the present `FiniteLatticeWilsonRandomScanHeatBathContractionData` exact-gap field cannot be instantiated with the current normalized carrier.

This is a normalization-layer mismatch, not a proof of the desired spectral estimate. The formal route must be repaired by separating the Markov/heat-bath gap from the normalized physical gap, or by inserting an explicit positive scale factor, for example

```text
lambda_HB <= 1 - rho
Delta_norm = s_HB * lambda_HB
```

or by using a correctly scaled continuous-time generator rather than directly identifying the normalized random-scan gap with `33/20`.

## What the repository currently proves

| Surface | Current reading |
|---|---|
| Finite Wilson Gibbs and conditional laws | Concrete definitions and finite identities are present |
| `P_e` and `Q_e` algebra | Idempotence, ranges, kernels, decomposition, and local fluctuation-energy identities are present |
| Detailed balance | Pointwise and finite product-sum reversibility are present |
| Gibbs-pairing symmetry of `P_e` | Open PR #242; not yet on `main` |
| Dobrushin influence data structures | Present |
| Uniform Wilson Dobrushin estimate | Not proved |
| Random-scan contraction from Dobrushin data | Not yet derived |
| Heat-bath-to-physical-gap normalization | Not yet repaired |
| Hamiltonian / transfer / continuum propagation | Typed conditional implication route is present |
| Nontrivial physical continuum construction | Not proved unconditionally |
| Physical derivation of `33/20` | Not established |
| External mathematical consensus | Not claimed |

## Primary review anchors

| Topic | File |
|---|---|
| Short status anchor | `docs/current_proof_status.md` |
| Exact-gap dependency separation | `docs/exact_gap_layer_separation.md` |
| Exact normalized carrier | `MGAP4D/MathlibAnalytic/ExactGapReal.lean` |
| Internal `33/20` origin package | `MGAP4D/MathlibAnalytic/HamiltonianPVMSpectralExactGapValue.lean` |
| Finite Gibbs variance | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonGibbsRealExpectation.lean` |
| Single-link variance / Dirichlet form | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonSingleLinkHeatBathDirichlet.lean` |
| Projection `P_e` | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonSingleLinkHeatBathProjection.lean` |
| Linear projection | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonSingleLinkHeatBathLinearProjection.lean` |
| Fluctuation projection `Q_e` | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonSingleLinkHeatBathFluctuationProjection.lean` |
| Fluctuation energy | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonSingleLinkHeatBathFluctuationEnergy.lean` |
| Random-scan sweep | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonRandomScanHeatBathSweep.lean` |
| Dobrushin data | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonDobrushinMatrix.lean` and `FiniteLatticeWilsonUniformDobrushinMatrix.lean` |
| Detailed balance | `MGAP4D/MathlibAnalytic/FiniteLatticeWilsonSingleLinkHeatBathDetailedBalance.lean` |
| Reversible product sum | `MGAP4D/MathlibAnalytic/FiniteWilsonHeatBathForwardSumExplicit.lean` |
| Conditional Hamiltonian bridge | `MGAP4D/MathlibAnalytic/FiniteWilsonSingleLinkHeatBathHamiltonianBridge.lean` |
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

1. Complete Gibbs-pairing symmetry, self-adjointness, and `P_e`/`Q_e` orthogonality.
2. Repair the random-scan/physical-gap normalization mismatch.
3. Derive an operator contraction theorem from the finite and uniform Dobrushin packages.
4. Prove a genuine scale-uniform estimate for the non-Abelian Wilson conditional laws.
5. Construct the physical Hamiltonian/observable quadratic-form bridge.
6. Establish a nontrivial regular continuum limit and complete independent external review.

## Public claim boundary

Recommended wording:

```text
MGAP4D is a Lean 4 formal-development repository for a four-dimensional
Yang--Mills mass-gap proof architecture. It contains a concrete finite Wilson
heat-bath probability and operator lane, conditional Hamiltonian/transfer/OS
propagation theorems, and an internal normalized 33/20 audit carrier. The
uniform non-Abelian estimate, normalization bridge, physical continuum
construction, and independent derivation of the physical mass gap remain open.
```
