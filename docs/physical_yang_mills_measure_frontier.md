# Physical four-dimensional Yang--Mills measure frontier

The finite compact-gauge Wilson Gibbs measures are genuine Mathlib probability measures. The physical weak-limit layer pushes the varying lattice laws into one fixed Polish configuration space and uses Mathlib weak convergence of `ProbabilityMeasure`.

## Closed measure-theoretic and topological spine

```text
finite-lattice deterministic or expectation estimate
  -> uniform coercive moment
  -> canonical Markov tail
  -> compact containment
  -> tightness
  -> Prokhorov subsequence
  -> physical continuum weak limit
```

The branch contains:

- a fixed physical Polish/Borel carrier and measurable lattice interpolation maps;
- pushforward lattice probability measures and an actual continuum `ProbabilityMeasure`;
- weak convergence together with lattice spacing tending to zero and physical volume tending to infinity along the extracted subsequence;
- bounded-continuous observable convergence and continuous-symmetry inheritance;
- exact pushforward `lintegral` identities, canonical compact sublevels, and automatic Markov tails;
- observable domination, expectation-supremum, pointwise, and affine Wilson-action routes;
- exact Wilson-action decomposition into plaquette energies;
- compactness-generated plaquette-energy maxima.

## Exact periodic four-dimensional geometry

For the periodic four-dimensional hypercubic geometry, Mathlib proves

```text
#Vertex(L) = L^4,
#AxisPair = 6,
#Plaquette(L) = 6 * L^4.
```

A `PeriodicHypercubicPlaquetteFamily` identifies each abstract Wilson plaquette type with this concrete periodic geometry.

Define

```text
plaquetteVolume_n = 6 * L_n^4,
reciprocalPlaquetteScale_n = plaquetteVolume_n^-1.
```

Positive side length implies that `plaquetteVolume_n` is nonzero and finite, so `ENNReal.inv_mul_cancel` gives

```text
reciprocalPlaquetteScale_n * plaquetteVolume_n = 1.
```

This removes the separate scaled-cardinality hypothesis on the reciprocal-volume route.

## Unitary normalized traces

For a complex unitary matrix `U : U(N)`, define

```text
normalizedUnitaryRealTrace(U)
  = (1 / N) * sum_i Re(U_ii).
```

Mathlib's `entry_norm_bound_of_unitary` and `RCLike.abs_re_le_norm` give

```text
|Re(U_ii)| <= norm(U_ii) <= 1.
```

Finite-sum monotonicity and division by the positive rank then prove

```text
-1 <= normalizedUnitaryRealTrace(U) <= 1.
```

`WilsonUnitaryTraceEnergyFamily` records the standard Wilson presentation

```text
E_n(g) = 1 - normalizedUnitaryRealTrace(rho_n(g)).
```

It automatically supplies the abstract normalized-character receipt and the universal energy bound

```text
E_n(g) <= 2.
```

## Special-unitary gauge realization

The determinant-forgetting map

```text
SU(N) -> U(N)
```

is formalized as a monoid homomorphism. Consequently a fixed-rank special-unitary representation

```text
rho_n : Gauge_n ->* SU(N)
```

produces the unitary-trace and normalized-character receipts automatically.

The still more concrete structure

```lean
WilsonSpecialUnitaryGaugeFamily
```

asks for scale-wise group equivalences

```text
Gauge_n ≃* SU(N)
```

and the standard trace formula for the plaquette energy. This removes the separate representation receipt: the representation is generated from the group equivalence.

## Sharp normalized action bound

Combining the exact periodic cardinality, reciprocal plaquette scaling, and the unitary trace bound gives

```text
renormalizedWilsonAction_n(U)
  = (6 * L_n^4)^-1 * S_n^Wilson(U)
  <= 2.
```

The resulting `WilsonActionControlUniformPointwiseBound` generates the uniform Gibbs moment bound without a separate expectation estimate.

## Proper physical coercive functionals

For a possibly noncompact physical carrier, the practical constructor is

```lean
NaturalRadiusCoerciveFunctional.ofProperNNReal
```

Given a proper map

```text
Phi : PhysicalConfiguration -> NNReal,
```

Mathlib derives:

- measurability of the coerced `ENNReal` functional;
- compactness of every natural-radius sublevel;
- the canonical physical coercive-functional receipt.

The `ENNReal`-valued proper-map constructor is also available, but because `ENNReal` is compact it is mainly useful when the physical carrier itself is compact.

## Current most concrete public constructor

The current endpoint is

```lean
continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicSpecialUnitaryGaugeProperNNRealFunctional
```

Its inputs are:

1. a `ContinuousCompactGaugeWilsonPhysicalEmbedding` into one fixed physical Polish carrier;
2. a `PeriodicHypercubicPlaquetteFamily`;
3. a `WilsonSpecialUnitaryGaugeFamily`, identifying every lattice gauge group with one fixed `SU(N)` and the plaquette energy with the normalized real-trace Wilson energy;
4. a proper functional `Phi : PhysicalConfiguration -> NNReal`;
5. the pointwise interpolation estimate

```text
Phi(interpolate_n(U))
  <= (6 * L_n^4)^-1 * S_n^Wilson(U).
```

It returns a `PhysicalFourDimensionalYangMillsWeakLimit`. The intermediate receipts for normalized characters, the universal plaquette-energy bound, compact maxima, normalized-action moments, compact sublevels, tightness, and Prokhorov extraction are constructed automatically.

The reciprocal plaquette scale is a canonical deterministic normalization route. It is not asserted to be the physically correct renormalized weak-coupling trajectory.

## Remaining analytic construction

A concrete non-Abelian four-dimensional construction must still provide:

1. a fixed gauge-invariant or distributional Polish carrier;
2. explicit interpolation or blocking maps;
3. a physically justified renormalized weak-coupling trajectory;
4. a concrete proper Sobolev/Besov-type `NNReal` functional;
5. the interpolation/coercivity estimate;
6. the concrete identification of the finite-lattice gauge systems and Wilson energy with the `SU(N)` receipt used here;
7. uniqueness, nontriviality, and interacting character of subsequential limits;
8. reflection positivity, Euclidean covariance, clustering, and Schwinger regularity in the limit;
9. Osterwalder--Schrader reconstruction and the final continuum Hamiltonian mass-gap connection.

The present files do not claim these remaining analytic facts. They prove that once these explicit analytic receipts are supplied, the passage from finite-lattice Wilson estimates to a physical subsequential continuum weak limit is a theorem rather than an opaque assumption.
