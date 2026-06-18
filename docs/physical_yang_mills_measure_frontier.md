# Physical four-dimensional Yang--Mills measure frontier

The finite compact-gauge Wilson Gibbs measures are genuine Mathlib probability measures.  The physical weak-limit layer pushes the varying lattice laws into one fixed Polish configuration space and uses Mathlib weak convergence of `ProbabilityMeasure`.

## Closed measure-theoretic and topological spine

The branch now formalizes the following implication chain:

```text
finite-lattice deterministic or expectation estimate
  -> uniform coercive moment
  -> canonical Markov tail
  -> compact containment
  -> tightness
  -> Prokhorov subsequence
  -> physical continuum weak limit
```

In particular, it contains:

- a fixed physical Polish/Borel carrier;
- measurable interpolation maps from scale-dependent lattice configuration spaces;
- pushforward lattice probability measures;
- an actual continuum `ProbabilityMeasure` and Mathlib weak convergence;
- preservation along the extracted subsequence of lattice spacing tending to zero and physical volume tending to infinity;
- convergence of every bounded continuous observable expectation;
- inheritance of continuous symmetries preserved by all approximating laws;
- exact pushforward `lintegral` identities, allowing moment hypotheses to be stated on the original finite lattices;
- canonical compact sublevels `K_n = {x | Phi x <= n + 1}` and automatic Markov tails `C / (n + 1) -> 0`;
- domination, expectation-supremum, uniform pointwise, and affine Wilson-action routes to the same tightness theorem;
- exact decomposition of the Wilson action into a finite sum of plaquette energies;
- compactness-generated maxima of continuous plaquette energies on compact gauge groups.

## Current most concrete constructor

The public constructor

```lean
continuous_compact_gauge_wilson_weak_limit_of_compactPlaquetteCardinalityEnvelope
```

requires two analytic receipts.

First, a physical coercive interpolation estimate:

```text
Phi (I_n U) <= scale_n * S_n^Wilson(U) + offset_n.
```

Second, an explicit finite-volume normalization envelope:

```text
scale_n * (# Plaquette_n * E_n^max) + offset_n <= C < infinity,
```

where

```text
E_n^max = max_{g in G_n} E_n(g)
```

is generated automatically by compactness of the gauge group and continuity of the plaquette energy.  Mathlib's finite-sum simplification proves

```text
sum_{p in Plaquette_n} E_n^max = # Plaquette_n * E_n^max,
```

so the earlier abstract finite-sum envelope and this cardinality form are connected by a proved conversion.

## Remaining analytic construction

A concrete non-Abelian four-dimensional construction must still provide:

1. a fixed gauge-invariant or distributional Polish carrier suitable for continuum gauge fields or observables;
2. explicit interpolation or blocking maps into that carrier;
3. a renormalized weak-coupling trajectory with lattice spacing tending to zero and volume tending to infinity;
4. a concrete Sobolev/Besov-type coercive functional with compact canonical sublevels;
5. the interpolation/coercivity estimate against the affine-renormalized Wilson action;
6. a concrete proof of the cardinality normalization envelope along the chosen trajectory;
7. uniqueness, nontriviality, and interacting character of subsequential limits;
8. reflection positivity, Euclidean covariance, clustering, and Schwinger regularity for the physical limit;
9. Osterwalder--Schrader reconstruction and the final continuum Hamiltonian mass-gap connection.

The present files do not claim these remaining analytic facts.  They prove that once the two explicit finite-lattice receipts above are supplied, the passage to a physical subsequential continuum weak limit is a theorem rather than an opaque assumption.
