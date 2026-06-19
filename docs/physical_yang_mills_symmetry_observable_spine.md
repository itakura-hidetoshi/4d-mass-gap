# Physical Yang--Mills symmetry and observable spine

This document records the typed consequences of compatible gauge symmetry for the physical weak-limit construction.

## Assumptions

A `PhysicalFourDimensionalYangMillsSymmetryLimit` contains:

1. one common Polish physical configuration carrier;
2. embedded lattice probability measures converging weakly to a continuum probability measure;
3. a symmetry type and a continuous action on the physical carrier;
4. invariance of every approximating probability measure under that action.

For the oriented Wilson route, `PhysicalGaugeAction` obtains the approximating invariance from scale-dependent lattice gauge transformations and interpolation equivariance.

## Measure preservation

The continuum action is bundled as

```lean
physical_yang_mills_symmetry_measurePreserving
```

and each approximating action as

```lean
physical_yang_mills_approximating_symmetry_measurePreserving
```

Therefore every measurable event satisfies

```text
mu_n(action(g)^-1 s) = mu_n(s),
mu_YM(action(g)^-1 s) = mu_YM(s).
```

## Observable laws

For every measurable observable `O`,

```text
Law_mu_n(O after action(g)) = Law_mu_n(O),
Law_muYM(O after action(g)) = Law_muYM(O).
```

The corresponding Lean theorems are

```lean
physical_yang_mills_approximating_symmetry_observable_law_invariant
physical_yang_mills_symmetry_observable_law_invariant
```

The target measurable space is arbitrary, so this includes joint finite-dimensional observables by choosing a product or function-valued codomain.

## Bounded continuous expectations

For every bounded continuous real observable `O`,

```text
E_mu_n[O(action(g, A))] = E_mu_n[O(A)],
E_muYM[O(action(g, A))] = E_muYM[O(A)].
```

Moreover,

```text
E_mu_n[O(action(g, A))] -> E_muYM[O(A)].
```

This is proved by exact symmetry invariance at every finite scale followed by weak convergence of the untransformed observable expectations.

## Two-point and connected correlations

For bounded continuous real observables `O1` and `O2`, the continuum law satisfies

```text
E[O1(g.A) O2(g.A)] = E[O1(A) O2(A)].
```

The connected correlation

```text
E[O1 O2] - E[O1] E[O2]
```

is therefore symmetry invariant. The same equalities hold at every embedded lattice approximation, and the transformed two-point and connected correlations converge to their continuum values.

The terminal theorems are

```lean
physical_yang_mills_symmetry_twoPoint_expectation_invariant
physical_yang_mills_symmetry_connectedCorrelation_invariant
physical_yang_mills_symmetry_transformed_twoPoint_expectation_converges
physical_yang_mills_symmetry_transformed_connectedCorrelation_converges
```

## Finite n-point moments

For a finite set of bounded continuous real observables, multiplication is taken in the pointwise bounded-continuous-function algebra. The resulting finite product satisfies symmetry invariance at every lattice scale and for the continuum law, and its transformed expectations converge to the continuum n-point moment.

```lean
physical_yang_mills_symmetry_nPoint_expectation_invariant
physical_yang_mills_approximating_symmetry_nPoint_expectation_invariant
physical_yang_mills_symmetry_transformed_nPoint_expectation_converges
```

In formulas, for a finite index set `s`,

```text
E_mu_n[(prod_{i in s} O_i)(g.A)]
  = E_mu_n[(prod_{i in s} O_i)(A)]
  -> E_muYM[(prod_{i in s} O_i)(A)].
```

The empty finite product includes the normalized zero-point observable as a special case.

## Gauge-invariant observable algebra

Pointwise fixed bounded continuous observables satisfy

```text
O(g.A) = O(A)
```

for every supplied symmetry `g` and configuration `A`. They form both

```lean
physicalYangMillsGaugeInvariantObservableSubring
physicalYangMillsGaugeInvariantObservableSubalgebra
```

inside `BoundedContinuousFunction Configuration ℝ`. Thus gauge-invariant observables are closed under constants, addition, negation, multiplication, and real scalar multiplication.

Membership is characterized by

```lean
mem_physicalYangMillsGaugeInvariantObservableSubalgebra_iff
```

and each element of the fixed real subalgebra has a lattice-to-continuum expectation limit:

```lean
physical_yang_mills_gaugeInvariantObservable_expectation_converges
```

Pointwise fixedness also identifies its transformed and untransformed expectations at every embedded scale and in the continuum:

```lean
physical_yang_mills_gaugeInvariantObservable_approximating_expectation_eq
physical_yang_mills_gaugeInvariantObservable_continuum_expectation_eq
```

## Aggregate import

```lean
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeSymmetryObservableSpine
```

exposes the measure, event, observable-law, expectation, correlation, finite n-point, and gauge-invariant observable-algebra layers together.

## Scope boundary

These are conditional transfer theorems. They require a continuous action on the selected physical carrier and interpolation equivariance with the finite lattice gauge transformations. They do not construct the final distributional continuum gauge group, prove uniqueness or nontriviality of the continuum measure, transfer all Osterwalder--Schrader axioms, perform OS reconstruction, or prove the Hamiltonian mass gap.
