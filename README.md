# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The repository deliberately separates three kinds of statements:

1. **same-root theorems** constructed from the actual finite Wilson model and transported through the explicit continuum/OS reconstruction;
2. **generic analytic theorems** that are already formalized but live on a separate abstract physical carrier; and
3. **open model-facing obligations** that are still required before a Clay-level Yang--Mills existence-and-mass-gap theorem can be claimed.

The repository does **not** currently claim a completed proof of the Clay Millennium problem. In particular, the canonical same-root construction has reached a normalized vacuum, a complete vacuum-orthogonal excitation sector, and a graph-closed self-adjoint OS Hamiltonian, but it does **not yet** prove a strictly positive coercive lower bound on that excitation Hamiltonian, and the scalar rational-time continuum carrier is not yet the full four-dimensional continuum gauge field.

## Repository status — 2026-08-20 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest theorem-bearing checkpoint:
  PR #1896
  formal: normalize the same-root OS vacuum and center the excitation semigroup

Canonical exact merge SHA:
  777e48e54b1bdb8028d624513568be476a415e1d

Checkpoint validation:
  PR Lean Fast Check #11202
  completed / success

Public landing branch:
  main

Detailed development plan:
  ROADMAP.md
```

Only results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative theorem status.

## Current proof picture

The main constructive lane is now substantially farther than the older reflection-invariance checkpoint.

```text
actual periodic-even compact SU(N) Wilson Gibbs model
  -> actual finite Wilson reflection positivity / OS Gram geometry
  -> one-sided primary reflection-fixed boundary readout
  -> reflection-completed rational path on the same finite Wilson source
  -> canonical primary plaquette normalized-trace scalarization
  -> same-root path-valued Prokhorov continuum law on ℚ -> ℝ
  -> continuum positive rational-cylinder OS reflection positivity       [#1802]
  -> continuum intrinsic reflection invariance                          [#1803]
  -> fixed-slot positive-semidefinite OS bilinear forms                  [#1804]
  -> OS separation quotients and fixed-slot Hilbert completions
  -> directed-system / algebraic direct-limit Hilbert construction
  -> rational-time OS contraction                                       [#1845]
  -> completed direct-limit contraction + exact rational semigroup laws
  -> canonical zero-time regular sector
  -> real-time strongly continuous contraction semigroup                 [#1884-#1885]
  -> dense right-generator / OS Hamiltonian                              [#1886]
  -> graph closure, positive resolvents, self-adjoint closed Hamiltonian  [#1887-#1888]
  -> Yosida strong/exponential approximation and semigroup recovery       [#1889-#1893]
  -> exact generator / closed-Hamiltonian identification                  [#1894]
  -> same-root vacuum and vacuum-orthogonal excitation sector             [#1895]
  -> vacuum normalization, centering, excitation semigroup package        [#1896]
  -> strictly positive same-root excitation coercivity                    [OPEN NOW]
```

The central change from the previous README is therefore:

> **Same-root continuum OS positivity and OS reconstruction are no longer the immediate blockers. The immediate mass-gap blocker is now a strictly positive quantitative lower bound on the exact same-root vacuum-orthogonal Hamiltonian domain.**

## 1. Actual finite Wilson root

The finite compact-gauge lane uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar measure and an actual periodic-even Wilson Gibbs law. Integrated finite-model results include:

```text
oriented lattice / plaquette geometry
Wilson action and Gibbs probability measure
finite Wilson reflection positivity / Gram-square identities
boundary-fibered positive-half observables
constructive gauge covariance of plaquette holonomy
constructive gauge invariance of normalized real trace-power observables
integer temporal covariance and finite reflection covariance.
```

The interacting reflection-fixed boundary law is kept as the actual Wilson marginal. It is not silently replaced by Haar measure at nonzero coupling.

## 2. Same-root primary scalar continuum law

The current canonical continuum OS reconstruction does **not** use the old false shortcut that the entire two-fixed-slice boundary-vacuum readout is positive-half local.

Instead, the constructive route isolates the **primary reflection-fixed spatial slice**, proves its finite positive-half locality, completes the path under reflection using the same Wilson source, and then scalarizes by the canonical primary plaquette normalized trace.

The fixed continuum carrier is

```text
ℚ -> ℝ.
```

It is the rational-time process of the selected primary plaquette scalar observable, not the complete gauge connection on `ℝ⁴`.

The path laws remain same-root pushforwards of the actual finite Wilson Gibbs measures. Factorial lattice spacing and explicit temporal-reach estimates give the eventual finite-slot admissibility needed for the Prokhorov limit.

### Continuum OS positivity — integrated

PR #1802 proves that every bounded-continuous cylinder supported on finitely many nonnegative rational times has nonnegative OS reflection form under the same Prokhorov continuum law.

Schematically,

```text
0 <= ∫ x, F(x) * F(Θ x) ∂ L.continuumMeasure,
Θ x q = x (-q).
```

This is model-derived from the actual finite Wilson OS theorem. Continuum positivity is not introduced as a new axiom.

PR #1803 then proves exact intrinsic reflection invariance of the same continuum law, and PR #1804 packages each fixed nonnegative rational slot sector into a symmetric positive-semidefinite real OS bilinear form.

## 3. Fixed-slot OS Hilbert spaces and the directed limit

For each finite nonnegative rational slot sector, the repository now has the genuine OS reconstruction chain

```text
bounded-continuous cylinder carrier
  -> OS seminorm / null space
  -> separation quotient
  -> real Hilbert completion.
```

Canonical slot inclusions are lifted isometrically through those Hilbert completions. The directed family is then assembled into an algebraic Hilbert direct limit and completed to a global same-root Hilbert carrier.

Time translation is descended compatibly through the same directed system rather than being reintroduced on an unrelated abstract Hilbert space.

## 4. Rational and real OS contraction semigroups

The crucial rational-time contraction is theorem-generated from the same-root midpoint identity and a shift-independent OS norm bound.

PR #1845 closes

```text
‖T_t x‖ <= ‖x‖
```

for every nonnegative rational time on the canonical fixed-slot OS carrier. The estimate is then transported through separation, fixed-slot Hilbert completion, the algebraic direct limit, and the completed direct limit.

The completed rational operators satisfy exact semigroup coherence:

```text
T_0 = I,
T_s T_t = T_(s+t).
```

Contractivity alone does not imply strong continuity at zero. The repository therefore defines the maximal **zero-time regular sector** justified by the constructed rational action.

On that sector, PR #1884 canonically extends the rational orbits to all `NNReal` times, and PR #1885 closes an actual endomorphism-valued strongly continuous contraction semigroup.

Thus, on the regular same-root Hilbert carrier,

```text
T_0 = I,
T_s T_t = T_(s+t),
‖T_t x‖ <= ‖x‖,
T_t x -> x as t -> 0+.
```

OS symmetry and positivity are retained on the real-time semigroup.

## 5. Same-root generator and graph-closed Hamiltonian

PR #1886 constructs the dense right-generator domain directly from strong difference quotients of the actual regular `C₀` semigroup and defines

```text
A_OS  = right generator,
H_OS  = -A_OS.
```

The same-root Hamiltonian is symmetric and nonnegative at the quadratic-form level and is sequentially closable.

PR #1887 packages the graph closures as Mathlib `LinearPMap`s, proves positive-shift Hille--Yosida bounds and surjectivity, and closes the graph Hamiltonian as self-adjoint.

PRs #1888-#1893 then build the standard positive resolvent and Yosida machinery on the same carrier:

```text
R_λ = (λ I + H̄)⁻¹,
J_λ = λ R_λ,
H_λ = λ (I - J_λ),
E_n(t) = exp(-t H_(2^n)).
```

The repository proves the expected contraction/strong-convergence properties and recovers the original regular OS semigroup as the strong Yosida exponential limit, without inserting a spectral-functional-calculus identity as a premise.

Finally, PR #1894 proves the exact identification

```text
D(A_OS) = D(H̄),
A_OS = -H̄,
H_OS = H̄
```

on the original same-root regular OS semigroup.

## 6. Canonical vacuum and excitation sector

PR #1895 constructs the vacuum from the literal constant-one cylinder in the empty finite rational slot sector. Vacuum invariance is derived from the actual same-root semigroup, not postulated.

The canonical vacuum satisfies

```text
T_t Ω = Ω,
A_OS Ω = 0,
H̄ Ω = 0.
```

The repository then defines the vacuum line and the exact excitation Hilbert carrier

```text
Ω⊥ = {x | inner ℝ Ω x = 0}.
```

Integrated consequences include:

```text
Ω⊥ is complete;
T_t preserves Ω⊥;
H̄ maps its exact closed-domain intersection into Ω⊥;
the restricted graph-closed Hamiltonian is formally symmetric.
```

PR #1896 evaluates the empty-slot constant-one OS norm against the continuum probability law and proves the exact normalization

```text
‖Ω‖ = 1,
inner ℝ Ω Ω = 1,
Ω != 0.
```

It also defines the canonical vacuum coefficient and centered vector

```text
c_Ω(x) = inner ℝ Ω x,
x° = x - c_Ω(x) • Ω,
```

and proves

```text
x° ∈ Ω⊥,
c_Ω(x) • Ω + x° = x,
T_t(x°) = (T_t x)°.
```

The real OS semigroup is corestricted to the complete excitation carrier with exact zero-time, additive-semigroup, and contraction laws.

## 7. Immediate frontier: strictly positive same-root coercivity

The canonical code now exposes the exact property that must be proved next on the same-root excitation Hamiltonian domain:

```text
FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt P m
```

which represents the lower bound

```text
m * ‖x‖^2 <= inner ℝ x (H̄ x)
```

for every vector in the exact vacuum-orthogonal closed Hamiltonian domain.

What is **not** yet proved is the existence of a strictly positive value:

```text
∃ m > 0,
  FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt P m.
```

This is the immediate mathematical mass-gap frontier.

The preferred route is constructive and same-root:

```text
actual finite Wilson / primary-scalar quantitative information
  -> a uniform positive excitation estimate that survives the continuum limit
  -> exact coercivity on the same-root closed Hamiltonian domain
  -> exponential decay on the same-root excitation semigroup
  -> positive spectral lower bound above the normalized vacuum.
```

No positive mass constant should be inserted as an assumption merely to activate already-existing abstract theorems.

## 8. Separate generic physical OS / mass lane

The repository also contains an older, highly developed generic physical OS/Hamiltonian lane proving, under its explicit abstract physical hypotheses,

```text
physicalYangMillsMass
  = physicalYangMillsOSInfraredMass
  = greatest full-sector uniform exponential semigroup decay rate.
```

That lane includes the generator-domain differential inequality, Mathlib scalar Gronwall, closure to the full vacuum-orthogonal sector, and graph-closed Hamiltonian variational mass comparison.

However, the generic lane lives on a separate abstract `PhysicalHilbert` / physical-OS interface. The repository does **not** currently have an exact theorem identifying that carrier with the newer same-root primary-scalar regular direct-limit Hilbert carrier.

Therefore no positive mass, spectral gap, or numerical value may be transferred between the two carriers without an explicit exact bridge.

## 9. Parallel signed-spatial symmetry lane

A separate finite-lattice geometry lane now contains the abstract signed spatial permutation action corresponding to the 48-element cubic signed-permutation group.

Integrated through PR #1876:

```text
signed spatial vertex action
  -> signed unit-step covariance
  -> signed boundary-step transport
  -> gauge-configuration pullback
  -> readback of the canonical swap/reflection generators
  -> exact composition law / monoid action on configurations.
```

Still open in that lane:

```text
plaquette-holonomy covariance for the full signed group
canonical scalar/cubic representation projection
cubic irrep identification
continuum-spin identification
glueball spectral or mass statements.
```

No glueball claim follows merely from the existence of the finite signed spatial action.

## 10. Full four-dimensional Yang--Mills construction remains open

The same-root scalar process is a genuine continuum observable law and now supports a genuine OS/Hilbert/Hamiltonian reconstruction. It is nevertheless only the selected primary plaquette scalar rational-time process.

A Clay-level existence theorem still requires a sufficiently rich four-dimensional interacting continuum Yang--Mills field/state, with the required model-derived package of

```text
Euclidean covariance
gauge structure / local gauge-invariant observable content
reflection positivity
regularity / temperedness or the chosen rigorous substitute
clustering / vacuum structure
finite-Wilson compatibility
physical nontriviality
and the relevant Hamiltonian mass-gap conclusion.
```

Those properties must be constructed from the model rather than retained as terminal assumptions.

## Numerical discipline

The following quantities remain logically distinct unless an explicit theorem identifies them:

```text
1/2
  finite high-temperature Z₂ geometric-transfer cap / coercivity constant

physicalYangMillsMass
  variational mass on the older generic physical OS/Hamiltonian interface

m
  any future strictly positive coercive constant proved on the new same-root
  vacuum-orthogonal regular Hamiltonian carrier

33/20
  normalized endpoint of a separate conditional exact-value route.
```

The repository does not identify `1/2` or `33/20` with the same-root Yang--Mills mass merely because those numbers occur elsewhere in the formal program.

## Key files near the current frontier

```text
MGAP4D/MathlibAnalytic/
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumOS.lean
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumReflectionInvariance.lean
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumOSBilinearForm.lean

  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSCarrierContraction.lean
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRationalSemigroup.lean
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularSector.lean

  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularClosedHamiltonian.lean
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonal.lean
  PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumNormalizedCentered.lean

  PeriodicHypercubicSpatialSignedPermutationConfigurationComposition.lean
```

## Validation and repository discipline

The authoritative workflow is intentionally conservative:

```text
ordinary PRs start from the exact authoritative SHA and begin as Draft
GitHub connector is the canonical repository-operation path
CI decisions use completed workflow / job / Lean-step results only
queued or in_progress CI is never treated as final evidence
do not append commits to a PR head while its CI is running
separate Lean/code failures from Actions/cache/external failures
keep development additive / tighten-only
never introduce sorry / admit / axiom / placeholder constants
fix the final head before Ready
re-check exact head, base, mergeability, reviews and threads before integration
green PRs are integrated by normal merge with the expected head pinned
record the actual merge SHA returned by the merge action
verify the authoritative branch is identical / ahead 0 / behind 0
start the next Draft from that exact SHA.
```

The public `main` branch is a landing surface; the authoritative theorem carrier is `formal/real-hilbert-uniform-coercive-strong-limit`.

## Claim boundary

MGAP4D does **not** currently claim:

- an unconditional interacting four-dimensional continuum `SU(N)` Yang--Mills construction;
- a completed Clay Millennium mass-gap proof;
- that the primary scalar rational-time process is the complete continuum gauge field;
- a strictly positive coercive constant on the new same-root vacuum-orthogonal Hamiltonian domain;
- a positive same-root spectral gap or positive same-root exponential decay rate;
- an exact identification of the newer same-root regular direct-limit Hilbert carrier with the older abstract `PhysicalHilbert` carrier;
- that the older generic `physicalYangMillsMass` theorem has already been instantiated on the newer same-root scalar carrier;
- that the finite signed spatial action already determines a continuum glueball spin/mass sector;
- that finite `Z₂` coercivity `1/2` is the compact-gauge physical Yang--Mills mass;
- that `33/20` has already been derived as a physical mass in fixed physical units.

The current proof-development principle is

```text
actual finite Wilson geometry
  -> same-root primary scalar continuum law
  -> model-derived continuum OS positivity
  -> same-root Hilbert / C0 semigroup / self-adjoint Hamiltonian
  -> normalized vacuum and exact excitation carrier
  -> strictly positive same-root excitation coercivity
  -> same-root decay / spectral gap
  -> extension to the full 4D interacting gauge-field theory
  -> only then any independent numerical normalization.
```

See `ROADMAP.md` for the current milestone order and completion criteria.
