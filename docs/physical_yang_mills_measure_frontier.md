# Physical four-dimensional Yang--Mills measure frontier

Finite compact-gauge Wilson Gibbs laws are Mathlib probability measures. The physical weak-limit layer pushes the scale-dependent laws into one fixed Polish carrier and uses weak convergence of `ProbabilityMeasure`.

## Closed spine

```text
signed periodic SU(N) Wilson law
  -> reciprocal-volume action bound
  -> uniform coercive moment
  -> Markov tail
  -> compact containment
  -> tightness
  -> Prokhorov subsequence
  -> physical continuum weak limit
```

The branch contains the physical carrier and interpolation maps, pushforward laws, scale and volume asymptotics, bounded-continuous observable convergence, exact pushforward integrals, compact sublevels, automatic tails, and the concrete signed periodic finite-volume input.

## Signed physical-link geometry

Configurations remain attached only to physical positive links. Every plaquette boundary stores a traversal orientation:

```text
forward step  -> A(e),
backward step -> A(e)^-1.
```

`periodicHypercubicFiniteOrientedGeometry` identifies the signed periodic four-dimensional lattice with the generic finite oriented geometry. The resulting generic oriented holonomy agrees definitionally with the signed periodic holonomy.

The compact-oriented gauge algebra proves:

```text
stepValue(gamma . A)
  = gamma(initial) * stepValue(A) * gamma(terminal)^-1,

Hol_p(gamma . A)
  = gamma(base p) * Hol_p(A) * gamma(base p)^-1.
```

Therefore the Wilson action and Gibbs exponent are gauge invariant. Coordinatewise left-right Haar invariance gives invariance of product Haar measure, and the tilted finite-volume Gibbs probability measure is gauge invariant for every measurable event.

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

## Standard SU(N) Wilson plaquette energy

For `U : SU(N)`, the canonical energy is

```text
E_W(U) = 1 - Re(Matrix.trace U) / N.
```

Using the inclusion `SU(N) -> U(N)`, `entry_norm_bound_of_unitary`, `RCLike.abs_re_le_norm`, and the matrix-trace identity, Mathlib proves

```text
0 <= E_W(U) <= 2,
Continuous E_W,
E_W(h * g * h^-1) = E_W(g).
```

`periodicHypercubicSpecialUnitaryWilsonSystem` combines this energy with the signed periodic geometry and normalized compact Haar measure. Its plaquette holonomy and Wilson action agree definitionally with the previously constructed signed periodic formulas.

Consequently,

```text
S_L^Wilson(A) <= (6 * L^4) * 2,
(6 * L^4)^-1 * S_L^Wilson(A) <= 2.
```

Thus this route needs no separate Gibbs expectation estimate.

## Physical interpolation and proper functional

`periodicHypercubicSpecialUnitaryPhysicalEmbedding` packages a sequence of positive side lengths, one fixed `SU(N)` rank, couplings, actual signed Gibbs probability laws, measurable interpolation maps into one Polish carrier, lattice spacings tending to zero, and physical volumes tending to infinity.

For a possibly noncompact physical carrier,

```lean
NaturalRadiusCoerciveFunctional.ofProperNNReal
```

turns a proper map

```text
Phi : PhysicalConfiguration -> NNReal
```

into a measurable `ENNReal` coercive functional with compact natural-radius sublevels.

## Current orientation-correct constructor

```lean
periodicHypercubicSpecialUnitaryWeakLimitOfProperNNRealFunctional
```

Inputs:

1. positive periodic side lengths `L_n`;
2. a fixed positive rank `N` and couplings `beta_n >= 0`;
3. measurable interpolation maps from the actual positive-link `SU(N)` configuration spaces into one fixed Polish physical carrier;
4. lattice spacing tending to zero and physical volume tending to infinity;
5. a proper `NNReal` physical functional;
6. the single deterministic interpolation estimate

```text
Phi(interpolate_n(A))
  <= (6 * L_n^4)^-1 * S_n^signed-Wilson(A).
```

The constructor returns a `PhysicalFourDimensionalYangMillsWeakLimit`. Finite-volume Haar normalization, gauge invariance, the sharp action bound `2`, Gibbs moment control, compact containment, tightness, and Prokhorov extraction are generated automatically.

The reciprocal plaquette scale is a deterministic normalization route, not a claim about the physically correct renormalized weak-coupling trajectory.

## Remaining analytic frontier

A complete non-Abelian construction must still supply a physically appropriate distributional continuum carrier, explicit interpolation or blocking maps, the justified renormalized coupling trajectory, a proper Sobolev/Besov-type functional, and the coercive interpolation estimate above. Uniqueness, nontriviality and interacting character of the continuum law, reflection positivity and the other OS properties in the limit, OS reconstruction, and the final Hamiltonian mass gap remain open.

The present files prove the concrete signed-periodic-finite-law-to-subsequential-weak-limit spine once those remaining analytic inputs are supplied. They do not claim the complete four-dimensional Yang--Mills construction or mass-gap theorem.
