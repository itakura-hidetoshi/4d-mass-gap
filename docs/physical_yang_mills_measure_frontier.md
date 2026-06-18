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

## Factorized normalization receipts

The compact plaquette-cardinality envelope

```text
scale_n * (#Plaquette_n * E_n^max) + offset_n <= C
```

is now generated from three independent receipts:

```lean
WilsonScaledPlaquetteCardinalityBound
WilsonCompactEnergyMaximumUniformBound
WilsonOffsetUniformBound
```

Thus geometric finite-volume growth, compact-group energy control, and affine offsets can be proved separately and then combined by Mathlib monotonicity and `ENNReal` finiteness lemmas.

## Exact periodic four-dimensional cardinality

For the periodic four-dimensional hypercubic geometry, Mathlib proves

```text
#Vertex(L) = L^4,
#AxisPair = 6,
#Plaquette(L) = 6 * L^4.
```

A `PeriodicHypercubicPlaquetteFamily` identifies each abstract Wilson plaquette type with this concrete periodic geometry. Consequently, the geometric normalization receipt becomes

```text
scale_n * (6 * L_n^4) <= C_volume.
```

## Canonical reciprocal plaquette scale

Define

```text
plaquetteVolume_n = 6 * L_n^4,
scale_n = plaquetteVolume_n^-1.
```

Positive side length implies that `plaquetteVolume_n` is nonzero and finite, so Mathlib's `ENNReal.inv_mul_cancel` gives the exact identity

```text
scale_n * plaquetteVolume_n = 1.
```

Therefore no separate geometric volume-bound hypothesis remains on this route.

The current most concrete public constructor is

```lean
continuous_compact_gauge_wilson_weak_limit_of_periodicHypercubicReciprocalScale
```

Its remaining inputs are:

1. a `PeriodicHypercubicPlaquetteFamily` identifying the lattice geometry;
2. a finite uniform bound on the compactness-generated maxima `E_n^max`;
3. a finite uniform offset bound;
4. the physical interpolation/coercivity estimate
   `Phi(I_n U) <= (6 * L_n^4)^-1 * S_n^Wilson(U) + offset_n`.

This reciprocal scale is a canonical deterministic normalization route. It is not asserted to be the physically correct renormalized weak-coupling trajectory.

## Remaining analytic construction

A concrete non-Abelian four-dimensional construction must still provide:

1. a fixed gauge-invariant or distributional Polish carrier;
2. explicit interpolation or blocking maps;
3. a physically justified renormalized weak-coupling trajectory;
4. a concrete Sobolev/Besov-type coercive functional with compact canonical sublevels;
5. the interpolation/coercivity estimate;
6. compact-energy maximum control, or a sharper scale-dependent energy estimate;
7. uniqueness, nontriviality, and interacting character of subsequential limits;
8. reflection positivity, Euclidean covariance, clustering, and Schwinger regularity in the limit;
9. Osterwalder--Schrader reconstruction and the final continuum Hamiltonian mass-gap connection.

The present files do not claim these remaining analytic facts. They prove that once the explicit analytic receipts are supplied, the passage from finite-lattice Wilson estimates to a physical subsequential continuum weak limit is a theorem rather than an opaque assumption.
