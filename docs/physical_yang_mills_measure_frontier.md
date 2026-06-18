# Physical four-dimensional Yang--Mills measure frontier

Finite compact-gauge Wilson Gibbs laws are Mathlib probability measures. The physical weak-limit layer pushes the scale-dependent laws into one fixed Polish carrier and uses weak convergence of `ProbabilityMeasure`.

## Closed spine

```text
finite-lattice estimate
  -> uniform coercive moment
  -> Markov tail
  -> compact containment
  -> tightness
  -> Prokhorov subsequence
  -> physical continuum weak limit
```

The branch contains the physical carrier and interpolation maps, pushforward laws, scale and volume asymptotics, bounded-continuous observable convergence, exact pushforward integrals, compact sublevels, and automatic tails.

## Periodic four-dimensional geometry

Mathlib proves

```text
#Vertex(L) = L^4,
#AxisPair = 6,
#Plaquette(L) = 6 * L^4.
```

For

```text
plaquetteVolume_n = 6 * L_n^4,
scale_n = plaquetteVolume_n^-1,
```

positivity of `L_n` and `ENNReal.inv_mul_cancel` give

```text
scale_n * plaquetteVolume_n = 1.
```

## Unitary matrix trace

For `U : U(N)`, define

```text
normalizedUnitaryRealTrace(U)
  = (sum_i Re(U_ii)) / N.
```

Using `entry_norm_bound_of_unitary` and `RCLike.abs_re_le_norm`, Mathlib proves

```text
-1 <= normalizedUnitaryRealTrace(U) <= 1.
```

The diagonal-sum definition is identified with the conventional matrix trace:

```text
normalizedUnitaryRealTrace(U)
  = Re(Matrix.trace U) / N.
```

The same formula is inherited by `SU(N)` through its canonical inclusion into `U(N)`.

## Standard Wilson plaquette energy

`WilsonSpecialUnitaryMatrixTraceFormulaFamily` records

```text
Gauge_n ≃* SU(N),
E_n(g) = 1 - Re Tr(g) / N.
```

It automatically generates the normalized-character receipt and

```text
E_n(g) <= 2,
E_n^max <= 2.
```

Together with periodic geometry and reciprocal scaling this gives

```text
(6 * L_n^4)^-1 * S_n^Wilson(U) <= 2.
```

Thus this route needs no separate Gibbs expectation estimate.

## Proper physical functional

For a possibly noncompact physical carrier,

```lean
NaturalRadiusCoerciveFunctional.ofProperNNReal
```

turns a proper map

```text
Phi : PhysicalConfiguration -> NNReal
```

into the measurable `ENNReal` coercive functional with compact natural-radius sublevels.

## Current constructor

```lean
continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryMatrixTraceProperNNRealFunctional
```

Inputs:

1. a physical Wilson embedding into a fixed Polish carrier;
2. periodic four-dimensional plaquette geometry;
3. a fixed-rank `SU(N)` gauge identification with Wilson energy `1 - Re Tr(U) / N`;
4. a proper `NNReal` physical functional;
5. the interpolation estimate

```text
Phi(interpolate_n(U))
  <= (6 * L_n^4)^-1 * S_n^Wilson(U).
```

The constructor returns a `PhysicalFourDimensionalYangMillsWeakLimit`. Normalized-character control, energy maxima, moment bounds, compact sublevels, tightness, and Prokhorov extraction are generated automatically.

The reciprocal plaquette scale is a deterministic normalization route, not a claim about the physically correct renormalized weak-coupling trajectory.

## Remaining analytic frontier

A concrete non-Abelian construction must still supply the continuum carrier, interpolation or blocking maps, the physically justified coupling trajectory, a proper Sobolev/Besov-type functional, the coercive interpolation estimate, and the concrete finite-lattice `SU(N)` realization. Uniqueness, nontriviality, reflection positivity and the other OS properties in the limit, OS reconstruction, and the final Hamiltonian mass gap also remain open.

The present files prove the finite-lattice-estimate-to-subsequential-weak-limit spine once those analytic inputs are supplied. They do not claim the complete four-dimensional Yang--Mills construction or mass-gap theorem.
