# Physical four-dimensional Yang--Mills measure frontier

The finite compact-gauge Wilson Gibbs measures are already constructed as genuine Mathlib probability measures.  The new physical weak-limit layer requires all approximating laws to be pushed into one fixed Polish configuration space and then uses the weak topology on `ProbabilityMeasure`.

## Closed in the new layer

- an actual continuum probability-measure carrier;
- lattice spacing tending to zero;
- physical volume tending to infinity;
- weak convergence in law on a fixed physical configuration space;
- convergence of every bounded continuous observable expectation;
- automatic passage of every continuous finite-lattice symmetry to the weak-limit measure;
- direct bundling of continuous compact-gauge Wilson Gibbs measures as `ProbabilityMeasure`.

## Remaining analytic construction

A concrete non-Abelian four-dimensional construction must still provide:

1. a fixed Polish distributional configuration space suitable for gauge fields or gauge-invariant observables;
2. measurable interpolation or blocking maps from every finite lattice configuration space into that carrier;
3. a renormalized coupling trajectory with lattice spacing tending to zero and volume tending to infinity;
4. tightness of the pushed-forward Wilson Gibbs laws in that topology;
5. identification of every subsequential weak limit and proof that it is nontrivial and interacting;
6. reflection positivity, Euclidean covariance, clustering, and Schwinger regularity for the physical limit.

These are not represented as completed facts by the new file.  The point of the layer is to replace opaque continuum-construction propositions by Mathlib probability measures and weak convergence, while proving symmetry inheritance once those analytic inputs are supplied.
