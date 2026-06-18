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

## Uniform plaquette-energy reduction

A pointwise uniform receipt

```lean
WilsonPlaquetteEnergyUniformBound
```

now automatically supplies

```lean
WilsonCompactEnergyMaximumUniformBound
```

by evaluating the pointwise estimate at the compactness-generated maximizer. A real-valued bound

```text
plaquetteEnergy_n(g) <= C_E
```

is converted directly to the finite `ENNReal` receipt.

## Normalized-character Wilson energy

`WilsonNormalizedCharacterEnergyFamily` records the standard presentation

```text
E_n(g) = 1 - chi_n(g),
-1 <= chi_n(g) <= 1.
```

Mathlib then proves

```text
E_n(g) <= 2,
E_n^max <= 2.
```

Together with the exact periodic cardinality and reciprocal plaquette scale, this yields the sharp deterministic estimate

```text
renormalizedWilsonAction_n(U)
  = (6 * L_n^4)^-1 * S_n^Wilson(U)
  <= 2.
```

The resulting `WilsonActionControlUniformPointwiseBound` generates the uniform Gibbs moment bound, tightness, and the Prokhorov weak limit once the physical coercive interpolation estimate is supplied.

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
continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicProperNNRealFunctional
```

Its inputs are:

1. a `ContinuousCompactGaugeWilsonPhysicalEmbedding` into one fixed physical Polish carrier;
2. a `PeriodicHypercubicPlaquetteFamily`;
3. a `WilsonNormalizedCharacterEnergyFamily`;
4. a proper functional `Phi : PhysicalConfiguration -> NNReal`;
5. the pointwise interpolation estimate

```text
Phi(interpolate_n(U))
  <= (6 * L_n^4)^-1 * S_n^Wilson(U).
```

It returns a `PhysicalFourDimensionalYangMillsWeakLimit`. The intermediate receipts for compact sublevels, plaquette maxima, normalized-action moments, tightness, and Prokhorov extraction are constructed automatically.

The reciprocal plaquette scale is a canonical deterministic normalization route. It is not asserted to be the physically correct renormalized weak-coupling trajectory.

## Remaining analytic construction

A concrete non-Abelian four-dimensional construction must still provide:

1. a fixed gauge-invariant or distributional Polish carrier;
2. explicit interpolation or blocking maps;
3. a physically justified renormalized weak-coupling trajectory;
4. a concrete proper Sobolev/Besov-type `NNReal` functional;
5. the interpolation/coercivity estimate;
6. a concrete compact-matrix-group realization of the normalized character receipt, or an equivalent sharper energy estimate;
7. uniqueness, nontriviality, and interacting character of subsequential limits;
8. reflection positivity, Euclidean covariance, clustering, and Schwinger regularity in the limit;
9. Osterwalder--Schrader reconstruction and the final continuum Hamiltonian mass-gap connection.

The present files do not claim these remaining analytic facts. They prove that once these explicit analytic receipts are supplied, the passage from finite-lattice Wilson estimates to a physical subsequential continuum weak limit is a theorem rather than an opaque assumption.
