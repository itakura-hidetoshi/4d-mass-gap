# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The repository deliberately separates:

1. theorem infrastructure that is already integrated;
2. concrete finite-Wilson / OS constructions that have been formalized from the model;
3. theorem bridges whose remaining model-facing premises are explicit; and
4. final physical construction and normalization obligations that remain open.

MGAP4D does **not** currently claim an unconditional construction of interacting four-dimensional continuum Yang--Mills theory and does **not** claim a completed proof of the Clay Millennium problem.

## Repository status — 2026-08-17 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Current authoritative head:
  082cbf7e8b8042d847e9e1d670f85969e078e883

Latest integrated checkpoint:
  PR #1736
  Normalize unregularized OS log decay by elapsed time

Public landing branch:
  main

Detailed development plan:
  ROADMAP.md
```

Only results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative theorem status. Historical or stale open PRs are not part of the canonical theorem state.

## Where the proof stands now

The repository has moved well beyond the former #1669/#1670 documentation frontier. The current integrated picture is best read as several interacting lanes:

```text
actual finite compact Wilson / OS geometry
  -> strict finite Wilson actual-analysis modes
  -> C0 / L2 / positive-time theorem bridge
  -> gauge-invariant normalized-trace-power reductions
  -> model-facing cross-scale / positive-time readout obligations remain

same-Wilson-source temporal path laws
  -> factorial spacing a_n = (n!)^-1
  -> exact rational path-law stationarity
  -> finite joint laws / moments / cumulants / connected Schwinger stationarity
  -> finite reflection covariance and finite Wilson Gibbs reflection invariance
  -> continuum same-root OS reconstruction obligations remain

completed physical OS Hilbert semigroup
  -> continuous, antitone, nonnegative physical correlation C_psi(t)
  -> additive convexity
  -> multiplicative midpoint inequality
  -> logarithmic convexity
  -> nonnegative antitone finite-difference effective masses
  -> canonical long-time effective-mass limit
  -> endpoint logarithmic decay per elapsed Euclidean time
  -> identification with a strictly positive physical mass remains open
```

The newest major advance is the third lane: the completed physical OS autocorrelation now has a fully formalized **unregularized long-time logarithmic-decay/effective-mass spine**.

## Current integrated theorem spine

### 1. Continuum OS, Hilbert completion, semigroup, Hamiltonian, and spectral infrastructure

The repository contains formal infrastructure for

```text
reflection-positive quotient and separation
real pre-Hilbert and Hilbert completion
strongly continuous symmetric contraction semigroups
generator-domain and graph-closed Hamiltonian interfaces
self-adjoint / symmetric operator interfaces
PVM and bounded-Borel spectral calculus
scalar spectral measures and support theorems
variational non-vacuum physical-mass interfaces.
```

These theorems transport consequences from supplied continuum construction data. They do not by themselves construct the interacting continuum Yang--Mills model.

### 2. Actual finite compact `SU(N)` Wilson / OS geometry

The finite compact-gauge lane uses

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar measure and contains actual periodic Wilson Gibbs laws, finite reflection positivity, completed finite OS Hilbert carriers, boundary-moment representations, interacting boundary marginals, and density-corrected `L²` transports.

The interacting reflection-fixed boundary law is treated as

```text
d mu_{partial,n} = m_{0,n}^2 d mu_{Haar,n},
```

not as Haar measure at nonzero coupling.

The positive-boundary Wilson/Fock strictness package reaches the actual-analysis sector, and PR #1670 integrates the theorem bridge from actual finite modes through `C⁰`, canonical `L²`, positive-time range statements, reconstructed vacuum-orthogonal excitation, and Hamiltonian/Rayleigh interfaces.

That theorem bridge deliberately leaves the final **concrete positive-time cylinder realization / cross-scale readout construction** model-facing rather than replacing it by global surjectivity, multiplicativity, or an abstract density assumption.

### 3. Gauge-invariant normalized-trace-power readout reductions

PRs #1671--#1675 sharpen the actual positive-time realization problem.

Integrated results include:

```text
cylinder-algebra multiplication before the merely-linear OS pullback
target-specific continuum finite-coordinate readout reductions
dense-interpolation uniqueness / gauge-invariance generation
cross-scale normalized-trace-power compatibility as an explicit same-root condition
conjugation invariance of normalized SU(N) trace powers
actual signed plaquette normalized-trace-power gauge invariance.
```

The remaining issue is not finite plaquette gauge invariance. It is the construction of the required **single physical bounded-continuous positive-time observables with the correct same-root finite readouts across scales**.

### 4. Rational temporal path stationarity from factorial spacing

The repository now contains a strong same-Wilson-source Euclidean stationarity lane.

For the canonical spacing

```text
a_n = (n!)^-1,
```

every fixed rational translation is eventually an exact lattice translation. This removes the floor-carry obstruction at all rational coordinates simultaneously.

The integrated chain proves:

```text
full rational path-law stationarity on R^Q
finite rational joint-law stationarity
stationarity of measurable finite-cylinder readouts
Bochner expectation invariance
finite n-point translation invariance
finite cumulant translation invariance
connected two-point translation invariance
labelled repeated-time connected Schwinger stationarity.
```

These are exact rational-time Euclidean statements. They do not by themselves construct a full `ℝ`-indexed continuum path probability law or Minkowski/Wightman theory.

### 5. Reflection geometry and finite Wilson Gibbs reflection invariance

The finite reflection lane now includes:

```text
rational path reflection topology
factorial eventual reflection alignment
finite temporal reflection covariance
finite rational-cylinder reflection covariance
full product-Haar reflection invariance
actual finite Wilson Gibbs reflection invariance.
```

This substantially strengthens the Euclidean/OS-facing finite geometry. A same-root passage from these finite facts to the required continuum reflection-positive physical construction remains a model-facing obligation.

### 6. Actual real-insertion physical OS two-point correlation

For a physical state `psi`, the completed symmetric OS semigroup supplies the autocorrelation

```text
C_psi(t) = <psi, T_t psi>.
```

The repository proves global uniform continuity of this correlation and constructs the actual real two-insertion function

```text
S_psi(t0,t1) = C_psi(|t1 - t0|),
```

with global uniform continuity and exact invariance under common real Euclidean-time translation.

The generic rational-to-real Schwinger extension machinery is also present. The remaining two-point same-root bridge is to identify the rational path-law connected two-point function with the rational restriction of this actual OS-semigroup correlation.

## Physical OS correlation regularity and decay — current frontier

This is the most recent integrated theorem chain.

### Additive and multiplicative convexity

For the completed symmetric physical OS semigroup, the repository proves

```text
C_psi((s+t)/2) <= (C_psi(s) + C_psi(t))/2
```

in its real-half-line form and, more strongly,

```text
C_psi((s+t)/2)^2 <= C_psi(s) C_psi(t).
```

The multiplicative midpoint inequality is obtained directly from Hilbert-space semigroup identities and Cauchy--Schwarz; no spectral representation or differentiability is assumed.

On the real half-line the zero-safe regularized form is also integrated:

```text
(C_tilde((s+t)/2) + epsilon)^2
  <= (C_tilde(s) + epsilon)(C_tilde(t) + epsilon),
```

for `epsilon >= 0`.

### Regularized logarithmic route and its obstruction

For every fixed `epsilon > 0`, the repository proves continuity and convexity of

```text
log(C_tilde(t) + epsilon),
```

then defines the corresponding finite-difference effective-mass secants and proves they are nonnegative and antitone along ordered equal-width intervals.

The resulting discrete sequence has a canonical long-time limit. However PR #1726 proves the decisive order-of-limits fact:

```text
fixed epsilon > 0
  => long-time regularized effective-mass limit = 0.
```

Thus a fixed positive additive floor cannot carry a positive asymptotic mass.

### Unregularized strict positivity and log convexity

PR #1727 proves finite-time injectivity of the strongly continuous symmetric semigroup and therefore, for every nonzero physical state,

```text
C_psi(t) > 0
```

at every finite nonnegative time.

This removes the zero obstruction and allows the logarithmic route to run directly at `epsilon = 0`.

The repository then proves:

```text
log C_tilde_psi is continuous and ConvexOn on [0,infinity)
unregularized effective-mass secants are nonnegative
later equal-width secants are <= earlier equal-width secants.
```

### Canonical unregularized long-time effective mass

For `h > 0` and nonzero `psi`, define the sampled effective-mass sequence

```text
M_h(n) = m(nh, nh+h).
```

It is proved nonnegative and antitone. The canonical fixed-step long-time limit is its conditional infimum:

```text
m_infinity,h = inf_n M_h(n),
```

and

```text
M_h(n) -> m_infinity,h,
0 <= m_infinity,h <= M_h(n).
```

Cesàro convergence and an exact telescoping identity then yield the current endpoint theorem:

```text
(log C_tilde_psi(0) - log C_tilde_psi(nh)) / (n h)
  -> m_infinity,h.
```

PR #1736 is the latest integrated checkpoint exposing this limit directly **per elapsed Euclidean time**.

This is a genuine long-time decay theorem for every nonzero state of the completed physical OS semigroup. It does **not yet** prove that `m_infinity,h` is strictly positive, independent of the sampling step in the strongest desired form, or equal to the repository's `physicalYangMillsMass`.

## Immediate proof frontiers

The main remaining obligations are now easier to state precisely.

### A. Identify OS long-time decay with physical spectral mass

Connect the new unregularized limit

```text
m_infinity,h
```

to the existing PVM / spectral-support / variational physical-mass interfaces. The final result must be model-derived; nonnegativity alone is not a mass gap.

Useful targets include the required sampling-step independence and the exact relation between asymptotic autocorrelation decay, the spectral support of the chosen non-vacuum state, and `physicalYangMillsMass`.

### B. Complete the same-root actual-Wilson-to-physical-OS readout

Construct the required cross-scale bounded-continuous positive-time normalized-trace-power observables from the existing actual Wilson/projective/cylinder geometry, with exact same-root finite readout identities.

Do not replace this by:

```text
global surjectivity of positiveHalfPullback
global multiplicativity of positiveHalfPullback
an arbitrary equivalence of carriers
an abstract Dense assumption
a duplicate physical Hilbert space.
```

### C. Complete the same-root path-law / OS two-point identification

Identify the rational path-law connected two-point function with the rational restriction of the actual completed physical OS autocorrelation. The extension and continuity machinery is already available once this exact same-root equality is supplied.

### D. Prove the selected moving-time finite-to-continuum residual

For the canonical theorem-generated finite Wilson slow states `phi_n`, prove the genuine quantitative estimate

```text
|| iota_n(K_n^2 phi_n) - T(2 a_n) iota_n(phi_n) ||
  <= 2 a_n delta_n,

delta_n -> 0.
```

Ordinary fixed-time convergence is not a substitute for this `o(a_n)` statement.

### E. Construct the interacting continuum Yang--Mills model

The final continuum probability/state, gauge content, reflection positivity, regularity, clustering/vacuum properties, finite-Wilson compatibility, and physical time-semigroup identification must be generated from the model rather than retained as terminal data.

### F. Close the physical exact-value normalization

The repository retains a conditional normalized R4 theorem route involving `33/20`, but a physical identity requires actual model-derived component extrema, sharpness, physical mass identification, and an independently constructed reference-time normalization.

## Numerical discipline

The following numerical surfaces remain distinct:

```text
1/2
  finite high-temperature Z2 geometric-transfer spectral cap /
  finite geometric Dirichlet coercivity constant

m_infinity,h
  state- and step-indexed unregularized OS long-time effective-mass / log-decay limit

physicalYangMillsMass
  variational mass of the reconstructed physical Hamiltonian

33/20
  normalized exact-value endpoint in the R4 theorem route,
  conditional on additional model-specific variational and normalization inputs.
```

No equality between these quantities is inferred merely because they occur in the same program.

## Key files around the newest frontier

```text
MGAP4D/MathlibAnalytic/
  PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelation*.lean
  PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularized*.lean
  ...UnregularizedNormalizedLogDecayOverTime.lean

  PhysicalYangMillsWilsonSU2*PositiveTime*.lean
  PhysicalYangMillsWilsonSU2*NormalizedTracePower*.lean

  PeriodicHypercubicEven*Rational*Stationarity*.lean
  PeriodicHypercubicEven*Reflection*.lean
```

The exact source of truth is the canonical branch itself; this list is only an orientation map.

## Validation and repository discipline

The authoritative workflow remains conservative:

```text
ordinary theorem PRs start from the exact authoritative SHA and begin as Draft
CI conclusions use completed run / job / step / artifact / log evidence only
queued or in_progress runs are not treated as final evidence
do not add commits to a branch while its CI is running
separate Lean/code failures from Actions/cache/external failures
fix the final head before Ready
re-audit base/head/mergeability/reviews/threads before merge
squash merge only
pin expected_head_sha at merge
verify the authoritative branch after integration.
```

Typical validation surfaces include `lake build` and the repository's changed-Lean fast-check scripts.

## Claim boundary

MGAP4D does **not** currently claim:

- an unconditional interacting four-dimensional continuum `SU(N)` Yang--Mills construction;
- a completed Clay Millennium mass-gap proof;
- that finite `Z₂` is the physical compact `SU(2)` / `SU(N)` theory;
- that finite coercivity `1/2` is the physical Yang--Mills mass;
- that the actual positive-time cross-scale readout problem is completely discharged;
- that rational path-law stationarity alone supplies a full real-path continuum field theory;
- that finite Wilson Gibbs reflection invariance alone supplies the final continuum OS construction;
- that the same-root rational path-law two-point function has already been identified with the physical OS-semigroup autocorrelation;
- that the unregularized long-time limit `m_infinity,h` is already proved strictly positive or equal to `physicalYangMillsMass`;
- that fixed positive regularization can retain a nonzero asymptotic mass;
- that fixed-time convergence proves the selected moving-time `o(a_n)` residual;
- that `33/20` has already been derived as a physical mass in fixed units.

The development principle remains:

```text
generic Mathlib theorem
  -> actual finite Wilson / plaquette / temporal geometry
  -> explicit same-root positive-time / path-law / continuum realization
  -> completed physical OS / Hamiltonian / spectral theorem
  -> only then physical mass identification and numerical normalization.
```

See `ROADMAP.md` for the current milestone order and completion criteria.
