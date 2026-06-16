# Current proof status

**Updated:** 2026-06-17  
**Latest merged checkpoint:** PR #241  
**Open continuation:** PR #242, not yet on `main`

## Status

The current source tree contains a concrete finite Wilson Gibbs and heat-bath lane:

```text
finite Wilson Gibbs law
  -> exact single-link conditional law
  -> Gibbs and conditional variances
  -> heat-bath Dirichlet form
  -> projection P_e
  -> fluctuation projection Q_e = I - P_e
  -> detailed balance
  -> reversible finite product-sum identity
```

On `main`, the projection algebra, local fluctuation-energy identity, exact detailed balance, and the theorem

```lean
finite_lattice_singleLinkHeatBath_reversible_product_sum
```

are present. Gibbs-pairing symmetry of `P_e` is proposed in PR #242 and is not yet merged.

The repository also contains conditional conversions from a uniform finite-volume coercivity estimate to Hamiltonian lower bounds, transfer contraction, continuum clustering, and OS/Wightman reconstruction. The required uniform non-Abelian estimate, physical quadratic-form identification, and nontrivial continuum construction remain open.

## Random-scan normalization issue

The current random-scan data require

```text
0 <= rho < 1
exactGapValueReal <= 1 - rho.
```

The source tree also proves

```lean
exactGapValueReal_above_one : 1 < exactGapValueReal
```

Since `0 <= rho` implies `1 - rho <= 1`, these hypotheses cannot hold together. The heat-bath/Markov gap must therefore be separated from the normalized physical gap, with an explicit scale bridge such as

```text
lambda_HB <= 1 - rho
Delta_norm = scale_HB * lambda_HB
scale_HB > 0.
```

Until that repair is made, the random-scan implication route has an unfilled normalization hypothesis.

## Exact `33/20` dependency

The numerical value enters in

```text
MGAP4D/MathlibAnalytic/HamiltonianPVMSpectralExactGapValue.lean
```

through the definition

```lean
hamiltonianPVMSpectralNormalized3320Value := (33 : Real) / 20.
```

`ExactGapReal.lean` projects `exactGapValueReal` from the package constructed there. Later spectral, R6, and R7 files transport the same value. Thus the lack of a literal `33/20` in `ExactGapReal.lean` is a local syntactic separation, not an independent physical derivation.

## Claim table

| Claim | Status |
|---|---|
| Exact finite Wilson conditional law | constructed |
| Gibbs variance and heat-bath Dirichlet form | constructed |
| Algebraic `P_e` and `Q_e` projections | constructed |
| Local variance/fluctuation-energy identity | proved |
| Exact detailed balance | proved |
| Reversible finite product sum | proved on `main` |
| Gibbs-pairing symmetry | open PR #242 |
| Gibbs orthogonality | open |
| Uniform Wilson influence estimate | open |
| Dobrushin-to-contraction theorem | open |
| Heat-bath/physical-gap scale bridge | open |
| Physical Hamiltonian identification | conditional |
| Continuum clustering | conditional |
| Nontrivial continuum Yang--Mills measure | open |
| Physical mass gap | open |
| Independent physical derivation of `33/20` | open |
| External consensus | not claimed |

## Next steps

1. Complete Gibbs-pairing symmetry and `P_e`/`Q_e` orthogonality.
2. Repair the heat-bath/physical-gap normalization.
3. Derive contraction from Dobrushin assumptions.
4. Prove scale-uniform Wilson influence bounds.
5. Construct the transfer Hamiltonian and quadratic-form bridge.
6. Establish a nontrivial continuum limit and independent review.

Lean theorem bodies are authoritative. Conditional structures and normalization carriers must not be presented as unconditional physical results.
