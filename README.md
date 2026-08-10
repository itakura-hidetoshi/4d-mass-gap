# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The repository now contains a large formal analytic spine connecting finite Wilson systems, Osterwalder--Schrader reconstruction, geometric-transfer estimates, finite-to-continuum variational recovery, and physical-Hamiltonian theorem interfaces. It does **not** currently contain an unconditional construction of interacting four-dimensional continuum Yang--Mills theory, and it does **not** claim a proof of the Clay Millennium problem.

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Public landing branch:
  main

Detailed development plan:
  ROADMAP.md

KuuOS reference bridge:
  docs/kuuos_reference_bridge.md
```

## Authoritative status — 2026-08-10 JST

```text
latest integrated theorem checkpoint:
  PR #1602
  Reduce independent OS classes to finite positive-definite Gram matrices

fixed PR head:
  5d4c2d72a6aadd9f559efa9d8c0effade79189b9

authoritative carrier / squash integration:
  3816c7600477f613c1a16d2dd38f0c177d11649c

validation:
  PR Lean Fast Check #9923
  run id 31350112541
  job id 93339185437
  completed / success

terminal build:
  Build completed successfully (8744 jobs)

artifact:
  lean-fast-check-log
  id 9048695428
  sha256:c5b6896e86ffd9eec562e9fcb68418d588d6dee9e6b5df89247b83d478f94c74

post-merge comparison:
  3816c7600477f613c1a16d2dd38f0c177d11649c
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

Only results merged into the authoritative carrier count as current theorem status. Open, Draft, stale, superseded, and closed-unmerged pull requests are historical or experimental unless their content is subsequently integrated.

## Executive summary

The current proof architecture is best read as seven connected lanes.

```text
A. continuum OS / Hamiltonian / PVM infrastructure

Euclidean and reflection-positive data
  -> OS separation and real Hilbert completion
  -> symmetric contraction semigroup
  -> graph-closed physical Hamiltonian
  -> PVM / bounded-Borel spectral calculus
  -> variational physical mass interfaces


B. finite compact SU(N) Wilson / OS geometry

actual periodic-even compact Wilson Gibbs law
  -> positive-time reflection form
  -> completed finite Wilson OS Hilbert space H_n^OS
  -> boundary-moment realization in boundary-Haar L2
  -> interacting boundary marginal m_{0,n}^2 dHaar
  -> actual compact projective observation / boundary recovery


C. finite Z2 geometric-transfer prototype

actual adjacent-slice transfer
  -> Perron / Doob analysis
  -> exact-marginal coordinate coupling
  -> volume-uniform excited-transfer cap 1/2
  -> geometric Dirichlet coercivity 1/2
  -> conditional strong-limit preservation


D. intrinsic finite Wilson rate and reverse variational recovery

centered finite Wilson excitation operator
  -> intrinsic logarithmic rate g_n
  -> positive two-step operator
  -> theorem-generated finite slow states phi_n
  -> symmetric-semigroup time averaging
  -> lossless moving Rayleigh estimate
  -> selected-sequence Mosco/Gamma-limsup interface


E. interacting common carrier across Wilson scales

actual interacting boundary marginals mu_{partial,n}
  -> countable infinite product probability
  -> canonical finite OS isometries into one common L2
  -> canonical common vacuum
  -> one common-product-to-physical isometry
  -> mass-free finite-to-continuum ambient carrier


F. physical mass and R4 variational exact-value route

forward intrinsic-rate inequality
  + selected slow-state reverse recovery
  -> conditional C.limit = physicalYangMillsMass

actual component forms
  -> component Rayleigh sInf/sSup extrema
  -> normalized R4 budget
  -> conditional referenceTime * physicalYangMillsMass = 33/20


G. current continuum kinematic reduction

common-product L2 is separable
  -> continuum physical Hilbert infinite-dimensionality suffices
  -> countable vacuum-orthogonal orthonormal sequence
  -> independent separated OS classes suffice
  -> finite positive-definite reflected OS Gram matrices suffice
  -> concrete strict OS nondegeneracy is the current kinematic frontier
```

The decisive advance since the previous documentation is that the main frontier is no longer the finite `Z₂` geometric gap or a generic projective-`L²` operator extension. Those layers remain integrated, but the current compact-Wilson-to-physical route has advanced substantially further.

The remaining hard obligations are now sharply localized:

```text
kinematic:
  construct a concrete countable continuum Wilson/OS observable family
  whose every finite reflected OS Gram matrix is positive definite

dynamical:
  prove the selected slow-state moving-time residual

    || iota_n(K_n^2 phi_n) - T(2 a_n) iota_n(phi_n) ||
      <= 2 a_n delta_n,
    delta_n -> 0

exact numerical endpoint:
  derive the actual R4 component decomposition,
  evaluate its six variational extrema,
  prove the sharp budget attainment,
  and fix the physical reference-time normalization independently.
```

## What is formally integrated

### 1. Continuum OS, semigroup, Hamiltonian, and PVM infrastructure

The continuum-facing theorem layer contains:

```text
reflection-positive quotient and separation
real pre-Hilbert and Hilbert completion
physical time semigroup interfaces
strong continuity and generator-domain machinery
graph closure of the physical Hamiltonian
symmetric/self-adjoint Hamiltonian interfaces
simple-function and bounded-Borel PVM calculus
quadratic scalar spectral measures
polarization, multiplicativity, and support theorems
variational non-vacuum mass interfaces.
```

For a supplied continuum construction spine, the repository can derive exact lower-spectrum consequences associated with its normalized exact-gap data. Those consequences are theorem transport from the supplied construction data; they do not by themselves construct the interacting continuum Yang--Mills measure.

### 2. Finite compact-Haar `SU(N)` Wilson Gibbs and heat-bath analysis

The compact finite-volume lane uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar measure. It includes:

```text
finite periodic Wilson Gibbs probability
exact one-link conditional laws
one-link heat-bath projections and kernels
Gibbs reversibility and Hilbert projection identities
conditional variance and Dirichlet forms
shared-plaquette localization
explicit bounded-test Dobrushin coefficients
finite Poincare/coercivity theorem generators with genuine L2 input.
```

The bounded-test coefficient package remains separate from any `L²` spectral-gap assertion: total-variation or bounded-test contraction is not silently promoted to a Hilbert-space gap.

### 3. Completed finite compact Wilson OS Hilbert spaces

For every selected finite Wilson scale, the repository carries the actual reflection-positive construction through completion.

A central integrated realization is

```text
H_n^OS
  -> L2(boundary Haar_n)
```

as a genuine real-linear isometry generated from the Wilson boundary moment. The actual interacting reflection-fixed boundary marginal is not Haar; it is represented by

```text
d mu_{partial,n} = m_{0,n}^2 d mu_{Haar,n},
```

with strictly positive boundary vacuum moment `m_{0,n}`. Reciprocal-vacuum multiplication gives the density-corrected isometry

```text
L2(boundary Haar_n)
  -> L2(mu_{partial,n}).
```

This avoids the incorrect shortcut of identifying an interacting Wilson boundary law with Haar measure.

### 4. Compact Wilson projective observation and boundary recovery

The finite compact-Wilson/projective route now works through actual observation diagrams rather than opaque equality assumptions.

At a selected scale, an actual compact `SU(N)` Wilson observation into finite projective coordinates and a boundary readout are used with `Measure.map_map` and the already-proved Wilson boundary pushforward theorem to generate the interacting boundary marginal identity.

Consequently the finite carrier route is theorem-generated as

```text
H_n^OS
  -> L2(boundary Haar_n)
  -> L2(interacting boundary marginal_n)
  -> L2(selected projective marginal_n).
```

The finite Wilson OS space is identified with the **exact range** of this embedding, not falsely with the whole raw marginal `L²` carrier.

### 5. Finite `Z₂` full geometric-transfer gap

The finite even-four-torus `Z₂` lane remains an important completed geometric prototype. It constructs genuine adjacent-slice Euclidean lattice time, residual Gauss projection, temporal-link summation, Perron--Doob structure, exact-marginal coupling, and a coordinate-response matrix.

On a positive volume-independent high-temperature interval, the integrated theorem gives

```text
every strictly excited normalized geometric-transfer eigenvalue <= 1/2
```

and the exact geometric Doob Dirichlet form satisfies coercivity with constant `1/2`.

This constant belongs to the finite `Z₂` geometric transfer theorem. It is **not** the physical Yang--Mills mass and is **not** the internal exact value `33/20`.

### 6. Ground-lifted defect and conditional strong-limit preservation

The finite `Z₂` spectral cap is converted into a whole-carrier ground-lifted defect bound

```text
(1/2) * ||f||^2 <= inner(D_H f, f).
```

For supplied asymptotically embedded varying-Hilbert convergence data, the exact constant is preserved at the limit, giving the corresponding limiting coercivity, real-spectrum enclosure, zero resolvent, and inverse-norm estimate.

The theorem proves **preservation under supplied convergence**. It does not replace the need to construct the actual thermodynamic/continuum convergence data for the physical compact gauge model.

### 7. Projective-limit `L²` cylinder and operator machinery

For a projective-limit probability measure, the repository constructs canonical finite-marginal pullback isometries, directed finite-coordinate cylinder subspaces, and the topological density theorem

```text
topologicalClosure (sup_J cylinderSubspace J) = top.
```

A uniformly bounded compatible finite-marginal operator family can then be glued on the algebraic cylinder core and extended uniquely to the complete continuum `L²` carrier.

This machinery is now supporting infrastructure rather than the immediate frontier.

### 8. Actual finite Wilson intrinsic rates and theorem-generated slow states

The actual completed finite Wilson excitation operator supplies the intrinsic scale rate

```text
g_n = - log ||T_n^exc|| / a_n.
```

The repository does not require finite-dimensional norm attainment or a one-step positive operator. Instead, for a bounded symmetric excitation operator `T`, Mathlib adjoint identities give positivity of `T^2` and

```text
||T^2|| = ||T||^2.
```

Applying the positive two-step Rayleigh/log-rate theorem produces actual unit finite slow states. At every scale one may select a canonical theorem-generated state `phi_n` whose two-step energy lies below

```text
g_n + a_n.
```

These slow states are not added as model data.

### 9. Symmetric-semigroup moving Rayleigh machinery

On the continuum physical Hilbert space, the repository develops the required moving-state control directly in Euclidean time.

For

```text
C_psi(t) = <psi, T_t psi>,
```

it proves positivity, antitonicity, midpoint identities, positivity and factorization of semigroup defects, and a lossless trapezoid estimate. For the normalized time average `A_h psi`, the graph-closed Hamiltonian satisfies the exact generator identity, and the two-step correlation defect rate `d_h` controls both numerator and denominator.

The key Rayleigh estimate is

```text
R(A_h psi) <= d_h / (1 - 2 h d_h)
```

whenever `2 h d_h < 1`, with no fixed coefficient loss. If scalar dominators converge while `h -> 0`, the correction also converges to the same limit.

### 10. Reverse Wilson mass recovery reduced to a selected sequence

The scalar route first proves

```text
physicalYangMillsMass <= C.limit
```

from a mass-free scalar two-step compatibility for the theorem-generated finite slow states.

The vector route then shows that it suffices to have an isometric finite-excitation embedding and

```text
|| iota_n(T_n^2 phi) - T(2 a_n) iota_n(phi) ||
  <= 2 a_n delta_n,

delta_n -> 0.
```

Finally the recovery hypothesis is weakened to the **single canonical slow-state sequence** `phi_n`. No all-vector moving-time estimate is required.

Under that selected-sequence residual, the integrated theorem chain yields:

```text
physicalYangMillsMass <= C.limit
nonzero vacuum-orthogonal continuum graph-domain excitation witness
```

and, together with the independent forward common-carrier direction,

```text
C.limit = physicalYangMillsMass.
```

This is a theorem generator: the selected moving-time `o(a_n)` residual is still a genuine model-specific obligation and is not claimed to be proved from the bare compact Wilson system yet.

### 11. Mass-free interacting common carrier across Wilson scales

The scale-wise common carrier no longer assumes false exact projectivity of interacting Gibbs measures at different lattice spacings.

For each scale, use the actual interacting boundary marginal `mu_{partial,n}`. Mathlib finite products and `Measure.infinitePi` construct the countable common probability

```text
mu_common = tensor/product over n of mu_{partial,n}.
```

Every finite completed OS Hilbert space then embeds isometrically as

```text
H_n^OS
  -> L2(boundary Haar_n)
  -> L2(mu_{partial,n})
  -> L2(mu_common).
```

Positive-half unit compatibility is theorem-generated after canonical sign normalization, so all finite OS vacua map to the same constant-one common vacuum without inserting an extra scale-wise vacuum normalization assumption.

### 12. One common-product physical realization generates all finite ambient maps

Instead of storing a separate finite-to-continuum physical embedding at every scale, the repository reduces the entire kinematic family to one vacuum-preserving map

```text
L2(mu_common) ->_linear_isometry P.PhysicalHilbert.
```

Once this one map exists, every finite Wilson OS-to-physical embedding, norm law, vacuum law, and mass-free excitation embedding is theorem-generated.

The remaining question is therefore not a family of arbitrary operators; it is the existence of this one common-product physical realization from the actual continuum OS geometry.

### 13. The common-product physical carrier reduced to strict OS nondegeneracy

The repository has progressively removed abstract kinematic inputs.

The reduction chain is now:

```text
opaque common-product physical isometry
  -> Hilbert-basis index embedding
  -> Hilbert-cardinal inequality
  -> continuum physical Hilbert is infinite-dimensional
  -> countable vacuum-orthogonal orthonormal excitation sequence
  -> countable linearly independent separated OS classes
  -> every finite reflected OS Gram matrix is positive definite.
```

The latest integrated PR #1602 proves the final generic equivalence needed here using Mathlib's finite-local linear-independence theorem and positive-definite Gram-matrix API.

Concretely, it is enough to construct a countable positive-time gauge-invariant continuum observable family `observable : ℕ -> P.Carrier` such that for every finite set of indices, the matrix

```text
G_ij = D.osBilinForm P.omega
         (P.toPositiveTime (observable i))
         (P.toPositiveTime (observable j))
```

is positive definite.

That finite strict Gram condition theorem-generates global linear independence of the separated OS classes, non-finite-dimensionality of the physical Hilbert space, the vacuum-orthogonal excitation family, the common-product physical realization, and hence the mass-free finite-to-continuum ambient carrier.

Reflection positivity alone supplies positive **semidefiniteness**, not this strict positive definiteness. Constructing a concrete infinite family with strict OS nondegeneracy is therefore the current kinematic construction problem.

### 14. R4 variational exact-value route

The exact-value lane is now phrased in terms of actual physical component forms and their variational Rayleigh extrema rather than free certificate coefficients.

For an actual component form `q`, the canonical lower and upper coefficients are identified with

```text
sInf { q(psi) / ||psi||^2 }
sSup { q(psi) / ||psi||^2 }
```

over genuine nonzero vacuum-orthogonal graph-domain physical states.

The normalized R4 budget is therefore a direct variational object. The repository proves structural implications such as

```text
referenceTime * physicalYangMillsMass = rayleighExtremaBudget
```

under the appropriate sharp-attainment and mass-identification hypotheses.

If the six actual component extrema are independently established as

```text
9/5, 1/10, 0, 1/10, 1/20, 1/10,
```

then their assembled budget is `33/20`.

The repository does **not** currently claim that those six evaluations, their physical decomposition provenance, the sharp attaining state, or the independent physical reference-time normalization have all been derived. Consequently `33/20` remains an internal/conditional normalized exact-value route, not a presently established physical Yang--Mills mass in fixed units.

## Current mathematical frontier

The current frontier has three independent parts.

### Kinematic continuum carrier

```text
choose an explicit countable family of actual continuum
positive-time gauge-invariant Wilson/OS observables

  -> prove every finite reflected OS Gram matrix is positive definite
  -> obtain global separated-class linear independence
  -> obtain infinite-dimensional physical Hilbert space
  -> theorem-generate the common-product physical isometry
  -> theorem-generate all finite mass-free ambient embeddings.
```

### Selected slow-state moving-time recovery

For the theorem-generated actual finite Wilson slow states `phi_n`, prove

```text
|| iota_n(K_n^2 phi_n) - T(2 a_n) iota_n(phi_n) ||
  <= 2 a_n delta_n,

delta_n -> 0.
```

This is the remaining dynamical Mosco/Gamma-limsup obligation needed by the current reverse variational route. Fixed-time strong convergence alone is not silently promoted to this rate-scaled moving-time estimate.

### Exact physical normalization

After the physical mass has been identified through the forward/reverse route, the numerical endpoint still requires independent proof of:

```text
the actual six-component R4 decomposition
the six component Rayleigh extrema
the sharp budget-attaining physical state or equivalent sharpness theorem
the model-derived physical reference-time normalization.
```

Only after those inputs are discharged can a normalized identity involving `33/20` be interpreted as a physical mass statement.

## Theorem boundary

| Surface | Status on the authoritative carrier |
|---|---|
| OS quotient, real Hilbert completion, semigroup, graph-closed Hamiltonian infrastructure | integrated |
| PVM / bounded-Borel spectral calculus and support theorems | integrated |
| Exact lower-spectrum consequences from supplied continuum construction data | integrated |
| Unconditional construction of the interacting continuum Yang--Mills measure | open |
| Finite compact-Haar `SU(N)` Wilson Gibbs / heat-bath infrastructure | integrated |
| Completed finite compact Wilson OS Hilbert spaces | integrated |
| Boundary-Haar `L²` realization of finite Wilson OS carriers | integrated |
| Interacting Wilson boundary marginal `m0^2 dHaar` and density-corrected `L²` transport | integrated |
| Selected compact Wilson projective observation -> interacting boundary marginal theorem | integrated |
| Finite `Z₂` full geometric-transfer spectral cap / coercivity `1/2` | integrated |
| Identification of finite `Z₂` with compact `SU(2)` / `SU(N)` continuum Yang--Mills | not claimed |
| Projective-limit `L²` cylinder density and compatible-operator extension | integrated |
| Actual finite Wilson intrinsic logarithmic rates and theorem-generated two-step slow states | integrated |
| Symmetric-semigroup moving Rayleigh correction | integrated |
| Reverse physical-mass theorem from selected slow-state two-step recovery | integrated conditionally on the residual |
| Common interacting boundary-product probability and finite OS embeddings | integrated |
| Canonical common Wilson vacuum after positive-half sign normalization | integrated |
| One common-product physical isometry -> all mass-free ambient maps | integrated theorem generator |
| Reduction of that physical isometry to continuum Hilbert infinite-dimensionality | integrated |
| Reduction further to linearly independent separated OS classes | integrated |
| Reduction further to finite positive-definite reflected OS Gram matrices | integrated |
| Strict positive definiteness for a concrete countable actual continuum Wilson observable family | open |
| Selected slow-state moving-time `o(a_n)` residual from actual compact Wilson/continuum dynamics | open |
| Conditional `C.limit = physicalYangMillsMass` once the current carrier and recovery data are supplied | integrated theorem consequence |
| Unconditional actual compact-Wilson-to-physical mass equality | open |
| Actual R4 component Rayleigh-extrema interpretation | integrated |
| Independent proof of all six required R4 extrema | open |
| Independent proof of R4 sharp budget attainment | open |
| Independent physical reference-time normalization | open |
| Internal normalized exact-value route involving `33/20` | integrated conditionally |
| `33/20` as a derived physical Yang--Mills mass in fixed units | not claimed |
| Clay Millennium theorem | not claimed |
| Independent external mathematical consensus | not claimed |

## Three constants that must not be conflated

The repository currently contains three mathematically different numerical surfaces.

```text
1/2
  finite high-temperature Z2 geometric-transfer spectral cap /
  ground-lifted defect coercivity constant

33/20
  internal normalized R4 exact-value target obtained only after
  additional model-specific variational and scale obligations

physicalYangMillsMass
  variational mass of the reconstructed physical Hamiltonian,
  whose identification with an intrinsic Wilson rate is conditional
  on the remaining actual carrier/recovery construction.
```

They are not interchangeable.

## What the repository does not currently claim

MGAP4D does not currently claim:

- an unconditional construction of interacting four-dimensional continuum `SU(N)` Yang--Mills theory;
- a completed proof of the Clay Millennium mass-gap problem;
- that finite `Z₂` is the physical compact `SU(2)` / `SU(N)` theory;
- that finite `Z₂` coercivity `1/2` is the physical Yang--Mills mass;
- that fixed-time convergence automatically implies the selected moving-time `o(a_n)` residual;
- that reflection positivity alone implies strict positive definiteness of the infinite observable-family OS Gram matrices;
- that the six R4 component extrema have already been derived from the final physical model;
- that `33/20` has already been established as a physical mass in fixed units.

The project is designed so that each remaining model-specific obligation is exposed explicitly rather than hidden inside a terminal certificate.

## Development principle

The preferred proof order remains:

```text
generic Mathlib theorem
  -> actual finite Wilson / OS specialization
  -> common-carrier or projective geometry
  -> continuum OS / Wightman / physical specialization
  -> only then numerical physical normalization.
```

Theorem statements, physical hypotheses, the exact internal `33/20` route, decay statements, and the finite coercivity constant `1/2` are not weakened merely to make downstream formalization easier.
