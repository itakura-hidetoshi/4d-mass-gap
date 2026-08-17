# MGAP4D Roadmap

This roadmap records the current proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-08-17 JST**.

Status labels used here:

- **Integrated** — merged into the authoritative theorem carrier;
- **Integrated reduction** — the theorem reduction is canonical, but an explicit model-facing construction remains;
- **Conditional route** — theorem composition is available once named hypotheses are supplied;
- **Open** — a genuine theorem or construction still required.

## Snapshot

```text
authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

authoritative head:
  082cbf7e8b8042d847e9e1d670f85969e078e883

latest integrated checkpoint:
  PR #1736
  Normalize unregularized OS log decay by elapsed time

public landing branch:
  main
```

Historical or stale open PRs are not authoritative. Only results merged into the theorem carrier count as the current proof state.

## Roadmap in one view

```text
actual finite compact Wilson / OS geometry                         [Integrated]
  -> actual-analysis strictness                                   [Integrated #1669]
  -> C0/L2/positive-time/reconstructed-excitation theorem bridge  [Integrated #1670]
  -> target-specific cross-scale gauge-invariant readout reduction[Integrated #1671-#1675]
  -> concrete same-root positive-time readout family              [OPEN]

factorial finite temporal geometry
  -> exact rational path-law stationarity                         [Integrated #1676-#1682]
  -> finite joint / moments / cumulants / Schwinger stationarity  [Integrated #1683-#1688]
  -> rational-to-real extension machinery                         [Integrated #1689-#1694]
  -> actual physical OS two-point real-insertion correlation      [Integrated #1695-#1699]
  -> same-root path-law <-> OS two-point identification           [OPEN]

finite reflection geometry
  -> rational-cylinder reflection covariance                     [Integrated #1700-#1705]
  -> product-Haar and finite Wilson Gibbs reflection invariance   [Integrated #1708,#1711]
  -> continuum same-root reflection-positive construction        [OPEN]

completed physical OS autocorrelation
  -> additive convexity                                           [Integrated]
  -> multiplicative midpoint inequality                           [Integrated #1713]
  -> regularized log convexity / effective masses                 [Integrated #1714-#1725]
  -> fixed positive epsilon asymptotic limit = 0                  [Integrated #1726]
  -> unregularized strict positivity / log convexity              [Integrated #1727-#1729]
  -> unregularized long-time effective-mass limit                 [Integrated #1730-#1732]
  -> Cesaro + telescoping + elapsed-time log-decay limit          [Integrated #1733-#1736]
  -> spectral-bottom / physical-mass identification               [OPEN NOW]

finite-to-continuum dynamics
  -> selected moving-time o(a_n) residual                         [OPEN]
  -> intrinsic Wilson rate = physical mass                        [Conditional route]

actual interacting continuum Yang--Mills construction             [OPEN]
actual R4 extrema + independent normalization                     [OPEN]
final physical mass-gap theorem                                   [OPEN]
```

---

# Architecture

The current program has eight logically distinct lanes.

## A. Continuum OS / Hamiltonian / spectral infrastructure

```text
reflection positivity
  -> separated OS quotient
  -> real Hilbert completion
  -> strongly continuous symmetric contraction semigroup
  -> generator / graph-closed Hamiltonian
  -> self-adjoint / PVM / bounded-Borel calculus
  -> scalar spectral measure / support
  -> variational physical mass.
```

**Status: Integrated as theorem infrastructure.**

Boundary: this infrastructure does not itself construct the interacting continuum Yang--Mills model.

## B. Actual finite compact Wilson / OS geometry

```text
periodic-even compact Wilson Gibbs law
  -> finite reflection positivity
  -> completed finite OS Hilbert carrier
  -> boundary-moment / boundary-Haar L2 realization
  -> interacting boundary marginal m0^2 dHaar
  -> positive-boundary Fock / Gram strictness
  -> actual boundary analysis and raw actual-analysis modes.
```

**Status: Integrated.**

## C. Actual Wilson positive-time / reconstructed-excitation bridge

```text
actual plaquette / normalized-trace modes
  -> bounded-continuous C0 representatives
  -> canonical C0 -> L2 transport
  -> positive-time submodule / pullback range factorization
  -> concrete trace-power range/readout interface
  -> reconstructed vacuum-orthogonal physical excitation
  -> Hamiltonian-domain / Rayleigh handoff.
```

**Status: theorem bridge integrated; concrete same-root cross-scale positive-time readout remains open.**

## D. Same-Wilson-source temporal path and Schwinger stationarity

```text
integer temporal stationarity
  -> factorial spacing a_n = (n!)^-1
  -> eventual exact alignment of every rational shift
  -> full rational continuum path-law stationarity
  -> finite rational joint laws
  -> n-point moments / cumulants / connected Schwinger functions.
```

**Status: Integrated through the rational-time Euclidean level.**

## E. Reflection geometry

```text
finite configuration reflection
  -> temporal reflection covariance
  -> factorial rational-cylinder alignment
  -> product-Haar reflection invariance
  -> finite Wilson Gibbs reflection invariance
  -> continuum same-root OS reflection-positive construction.
```

**Status: finite geometry and finite Gibbs law integrated; final continuum same-root step open.**

## F. Physical OS correlation regularity and long-time decay

```text
physical symmetric OS semigroup
  -> continuous / antitone / nonnegative correlation
  -> additive midpoint convexity
  -> multiplicative midpoint inequality
  -> log convexity
  -> effective-mass secant monotonicity
  -> long-time effective-mass limit
  -> endpoint log decay per elapsed Euclidean time.
```

**Status: Integrated through #1736.**

The current open question in this lane is the physical interpretation of that limit as a spectral mass and, ultimately, a strictly positive Yang--Mills mass.

## G. Finite-to-continuum dynamical recovery

```text
finite Wilson intrinsic rate g_n
  -> theorem-generated slow states phi_n
  -> moving-time comparison at 2 a_n
  -> continuum Rayleigh limsup
  -> reverse physical-mass inequality
  -> intrinsic-rate / physical-mass equality.
```

**Status: theorem machinery integrated; selected moving-time residual open.**

## H. Physical exact-value / normalization lane

```text
actual physical component forms
  -> component Rayleigh extrema
  -> sharp R4 budget
  -> actual physical mass identification
  -> independent reference-time normalization
  -> normalized 33/20 endpoint.
```

**Status: structural theorem route integrated conditionally; model-derived numerical inputs open.**

---

# Milestone ledger

## Milestone 0 — Authority, replay, and claim discipline

**Status: Integrated and permanent.**

Repository rules:

```text
start ordinary theorem PRs from the exact authoritative SHA
start as Draft
fix final head before Ready
use completed run/job/step/artifact/log evidence for CI conclusions
never treat queued/in_progress as final evidence
do not write to a branch while its CI is running
separate Lean/code failures from Actions/cache/external failures
re-audit base/head/mergeability/reviews/threads before merge
squash merge only
pin expected_head_sha at merge
verify the authoritative carrier after integration.
```

The public `main` branch is a landing surface. The theorem authority is `formal/real-hilbert-uniform-coercive-strong-limit`.

## Milestone 1 — Continuum OS, Hilbert, semigroup, Hamiltonian, and PVM infrastructure

**Status: Integrated.**

The repository contains the analytic infrastructure required to transport reflection-positive Euclidean data to a completed real physical Hilbert space, a strongly continuous symmetric physical time semigroup, Hamiltonian-domain interfaces, scalar spectral measures, and variational mass statements.

## Milestone 2 — Actual finite compact `SU(N)` Wilson / OS geometry

**Status: Integrated.**

Integrated surfaces include:

```text
finite periodic Wilson Gibbs probability
compact normalized Haar geometry
finite Wilson reflection positivity
completed finite OS Hilbert spaces
boundary-Haar and interacting-boundary L2 realization
selected finite/projective observation and boundary recovery.
```

The finite OS Hilbert carrier is identified with the exact range of its realization maps rather than an arbitrary raw `L²` carrier.

## Milestone 3 — Finite `Z₂` geometric-transfer theorem

**Status: Integrated supporting lane.**

The finite `Z₂` model proves the genuine geometric transfer cap / coercivity value

```text
1/2.
```

Permanent distinction:

```text
finite Z2 coercivity 1/2
  != compact SU(2)/SU(N) physical mass
  != unregularized OS long-time limit
  != normalized exact-value constant 33/20.
```

## Milestone 4 — Intrinsic finite Wilson rate and slow-state machinery

**Status: Integrated as theorem infrastructure.**

The repository defines

```text
g_n = -log ||T_n^exc|| / a_n
```

and theorem-generates finite two-step slow states. The continuum semigroup side contains time averaging, graph-domain identities, and moving Rayleigh estimates for reverse variational recovery.

## Milestone 5 — Actual positive-boundary Wilson strictness to actual analysis

**Status: Integrated — PR #1669.**

The actual finite Wilson package reaches:

```text
positive-boundary temporal Wilson factorization
protected strict Wilson/Fock Gram structure
nonzero actual boundary analysis operator
inverse interacting-boundary L2 density transport
positive-density normalized-trace witnesses
open-half nonzero probes
factorized actual-analysis nonzero criteria
Hilbert-Schmidt / Gram convergence
strict centered actual-analysis output infrastructure.
```

## Milestone 6 — Reconstructed physical-excitation theorem bridge

**Status: Integrated — PR #1670.**

The former active Draft is now canonical.

Integrated consequences include:

```text
actual plaquette/cylinder C0 closure
canonical bounded-continuous -> L2 transport
OS carrier ≃ positive-time submodule
finite positive-half observable range = coherent pullback range
trace-power readout reduced to concrete finite range membership
reconstructed nonzero vacuum-orthogonal excitation theorem route
Hamiltonian-domain / Rayleigh / physical-mass handoff.
```

The remaining premise is intentionally concrete: actual finite cylinder / positive-time realization from the same Wilson/projective geometry.

## Milestone 7 — Target-specific continuum readout and actual gauge invariance

**Status: Integrated reduction — PRs #1671--#1675.**

The realization problem is narrowed to the physically required targets.

Integrated results include:

```text
cylinder multiplication handled before the linear OS pullback
continuous finite-coordinate / scalar-readout reductions
Tietze extension as topology only, not hidden gauge invariance
dense-interpolation generation of global physical gauge invariance
cross-scale trace-power compatibility as an explicit same-root condition
normalized SU(N) trace-power conjugation invariance
actual signed plaquette normalized-trace-power gauge invariance.
```

**Still open:** construct a single same-root physical bounded-continuous positive-time observable family realizing the required trace-power targets across scales.

## Milestone 8 — Factorial spacing and full rational path-law stationarity

**Status: Integrated — PRs #1676--#1682.**

The canonical spacing

```text
a_n = (n!)^-1
```

is positive, tends to zero, and eventually aligns every fixed rational time exactly with the lattice.

This yields exact full-path stationarity on the rational continuum path carrier:

```text
forall r : Q,
  map (rationalTranslation r) mu_cont = mu_cont.
```

This is a full joint path-law statement on `ℝ^ℚ`, not a one-coordinate marginal argument.

## Milestone 9 — Finite joint laws, moments, cumulants, and connected Schwinger stationarity

**Status: Integrated — PRs #1683--#1688.**

The full rational path-law equality is projected to:

```text
finite rational joint laws
measurable finite-cylinder readouts
Bochner expectations
finite n-point products
centered products
finite cumulants
connected two-point correlations
labelled repeated-time connected Schwinger functions.
```

All are exactly invariant under common rational Euclidean-time translation.

## Milestone 10 — Rational-to-real extension infrastructure and actual OS two-point function

**Status: Integrated theorem infrastructure; same-root identification open — PRs #1689--#1699.**

Integrated layers include:

```text
density of rational tuples in real tuples
continuous common-shift uniqueness
uniform-extension machinery from rational insertion tuples
uniform continuity of actual physical OS autocorrelations
actual real-insertion OS two-point correlation
exact common real-time translation invariance.
```

For a physical state `psi`, the actual real two-point object is built from the OS semigroup as

```text
S_psi(t0,t1) = C_psi(|t1-t0|).
```

**Still open:** prove the exact same-root equality identifying the rational path-law connected two-point function with the rational restriction of this physical OS two-point object.

## Milestone 11 — Finite temporal reflection and Wilson Gibbs reflection invariance

**Status: Integrated at finite / rational-cylinder level — PRs #1700--#1711.**

Integrated results include:

```text
rational path reflection map
factorial eventual reflection alignment
configuration reflection / integer temporal conjugacy
finite rational-cylinder reflection covariance
full product normalized-Haar reflection invariance
actual finite Wilson Gibbs reflection invariance.
```

**Still open:** generate the final continuum same-root reflection-positive physical construction rather than merely retaining continuum OS input data.

## Milestone 12 — Additive convexity of physical OS correlations

**Status: Integrated — PRs #1696,#1703,#1707,#1710,#1712.**

The exact squared-norm midpoint defect yields ordinary midpoint convexity, which is promoted to full real-half-line convexity:

```text
ConvexOn R (Ici 0) C_tilde_psi.
```

No spectral representation or differentiability is used.

## Milestone 13 — Multiplicative midpoint inequality and regularized log convexity

**Status: Integrated — PRs #1713--#1715.**

The physical correlation satisfies

```text
C_psi((s+t)/2)^2 <= C_psi(s) C_psi(t).
```

After transfer to the real half-line, for every `epsilon >= 0`,

```text
(C_tilde((s+t)/2)+epsilon)^2
  <= (C_tilde(s)+epsilon)(C_tilde(t)+epsilon).
```

For `epsilon > 0`, this gives a positive continuous function whose logarithm is convex on `[0,infinity)`.

## Milestone 14 — Regularized effective-mass sequence and long-time limit

**Status: Integrated — PRs #1716--#1725.**

For fixed `epsilon > 0` and `h > 0`, finite-difference effective masses are proved:

```text
nonnegative
antitone on successive equal-width intervals
convergent to a canonical conditional infimum.
```

Cesàro convergence and exact telescoping identify the limit with normalized endpoint regularized logarithmic decay, including the elapsed-time form.

## Milestone 15 — Fixed-positive-regularization obstruction

**Status: Integrated — PR #1726.**

The regularized route is diagnostically complete:

```text
fixed epsilon > 0
  => (L_epsilon(0)-L_epsilon(nh))/(nh) -> 0
  => long-time regularized effective-mass limit = 0.
```

This is an order-of-limits theorem. A fixed positive additive floor cannot encode a positive asymptotic mass.

No existing physical mass, exact-value, finite-coercivity, or moving-time theorem is weakened by this result.

## Milestone 16 — Unregularized finite-time strict positivity and log convexity

**Status: Integrated — PRs #1727--#1729.**

For every nonzero physical state, finite-time injectivity of the strongly continuous symmetric semigroup implies

```text
C_psi(t) > 0
```

for every finite `t >= 0`.

Therefore the repository can work directly with

```text
log C_tilde_psi
```

without positive additive regularization. Its logarithm is continuous and convex on the real half-line, and the corresponding finite-difference effective masses are nonnegative and antitone.

## Milestone 17 — Canonical unregularized long-time effective-mass limit

**Status: Integrated — PRs #1730--#1732.**

For `h > 0`, define

```text
M_h(n) = m(nh, nh+h).
```

Then

```text
M_h is Antitone
0 <= M_h(n)
m_infinity,h := inf_n M_h(n)
M_h(n) -> m_infinity,h
0 <= m_infinity,h <= M_h(n).
```

This constructs a canonical finite-step long-time effective-mass limit for every nonzero physical state.

It does **not** yet prove strict positivity of that limit.

## Milestone 18 — Unregularized Cesàro / telescoping / elapsed-time log decay

**Status: Integrated — PRs #1733--#1736. Current authoritative checkpoint.**

The repository proves:

```text
Cesaro means of M_h -> m_infinity,h
sum_{i<n} M_h(i)
  = (log C_tilde_psi(0) - log C_tilde_psi(nh)) / h
```

and therefore

```text
(log C_tilde_psi(0) - log C_tilde_psi(nh)) / (n h)
  -> m_infinity,h.
```

This is the current endpoint: the unregularized physical OS autocorrelation has a canonical long-time logarithmic decay rate along every fixed positive sampling step.

---

# Current open frontiers

## Milestone 19 — Identify the OS log-decay limit with spectral support / physical mass

**Status: OPEN — immediate analytic frontier.**

The next theorem package should connect

```text
m_infinity,h
```

to the existing self-adjoint / PVM / scalar spectral-measure infrastructure.

The intended hierarchy is:

```text
physical OS autocorrelation
  -> Hamiltonian spectral/Laplace representation or existing equivalent bridge
  -> bottom of the spectral support seen by psi
  -> asymptotic logarithmic decay
  -> statewise spectral mass.
```

Then prove the additional statement actually needed to reach `physicalYangMillsMass`.

Important distinctions:

- `m_infinity,h >= 0` is already proved;
- strict positivity is **not** already proved;
- sampling-step independence should be theorem-generated, not assumed;
- equality with the global physical mass requires the correct non-vacuum spectral state/family and variational comparison.

If the repository's existing spectral calculus does not yet identify `T_t` with the required `exp(-tH)` functional calculus on the completed physical carrier, that bridge is the first submilestone rather than an implicit assumption.

## Milestone 20 — Complete same-root actual-Wilson positive-time readout

**Status: OPEN — immediate model-facing frontier.**

Construct the required normalized-trace-power physical observables from the actual Wilson/projective/cylinder root.

Required properties include, as needed by the existing reductions:

```text
bounded continuity
exact same-root finite readout
cross-scale compatibility
physical gauge invariance
positive-time membership.
```

Do **not** assume:

```text
global surjectivity of Q.positiveHalfPullback
global multiplicativity of Q.positiveHalfPullback
abstract Dense of the entire bounded-continuous carrier
a duplicate physical Hilbert space
A†A = Euclidean time evolution.
```

Once this is discharged, the already integrated #1670 theorem bridge produces the reconstructed nonzero physical excitation and its downstream Hamiltonian/Rayleigh interfaces.

## Milestone 21 — Same-root path-law / physical-OS two-point identification

**Status: OPEN.**

Prove the pointwise rational equality that identifies the connected two-point function from the factorial same-Wilson-source rational path law with the rational restriction of the actual physical OS-semigroup correlation.

The extension machinery is already available. This milestone should not add a second continuum field carrier merely to force the equality.

## Milestone 22 — Selected slow-state moving-time residual

**Status: OPEN — principal finite-to-continuum dynamical frontier.**

For the canonical theorem-generated finite slow states `phi_n`, prove

```text
|| iota_n(K_n^2 phi_n) - T(2 a_n) iota_n(phi_n) ||
  <= 2 a_n delta_n,

delta_n -> 0.
```

Equivalently, the residual is `o(a_n)`.

Ordinary fixed-time convergence is not a substitute. The estimate should come from genuine quantitative finite-to-continuum semigroup comparison, Mosco/Trotter--Kato style control, or another model-derived selected-sequence argument.

## Milestone 23 — Intrinsic finite Wilson rate equals physical mass

**Status: Conditional route integrated; actual closure open.**

The forward and reverse variational theorem infrastructure is already present. Once the required ambient same-root realization and Milestone 22 are discharged, theorem composition can identify the intrinsic finite Wilson rate limit with the physical mass.

This equality is not currently an unconditional theorem of the bare compact Wilson model.

## Milestone 24 — Global common-product physical realization / strict continuum OS family

**Status: OPEN as a separate global kinematic lane.**

The earlier reduction remains relevant when the full common-product physical isometry is required:

```text
concrete countable positive-time continuum observables
  -> every finite reflected OS Gram matrix positive definite
  -> separated OS classes linearly independent
  -> physical Hilbert infinite-dimensional
  -> common-product physical isometry theorem-generated.
```

The target-specific reconstructed-excitation route does not by itself assert this full global realization.

## Milestone 25 — Interacting continuum Yang--Mills construction

**Status: OPEN.**

The final model must construct, rather than retain as terminal data, the appropriate continuum objects and properties, including as needed:

```text
nontrivial interacting continuum probability/state
gauge covariance / gauge content
reflection positivity
regularity / temperedness
clustering and/or vacuum uniqueness inputs
compatibility with finite Wilson approximants
physical time-semigroup identification.
```

This is indispensable for a final Clay-level claim.

---

# Exact-value and physical-normalization milestones

## Milestone 26 — Actual R4 decomposition and component variational extrema

**Status: Structural theorem layer integrated; model-derived values open.**

For actual physical component forms, the repository identifies canonical coefficients with genuine Rayleigh-set `sInf` / `sSup` extrema.

Still required:

```text
derive the final component decomposition from the actual model
prove all required form/domain bounds
evaluate the required component extrema
prove sharp budget attainment or an equivalent sharpness theorem.
```

No coefficient may be chosen merely to manufacture the target rational number.

## Milestone 27 — Independent physical normalization and the `33/20` endpoint

**Status: Conditional theorem assembly integrated; physical derivation open.**

The normalized exact-value route retains the target

```text
33/20.
```

A physical identity involving that value requires all of the following independently:

```text
actual physical mass equality
actual model-derived R4 extrema
sharp combined budget
physical referenceTime / unit normalization.
```

Only then may an identity of the form

```text
referenceTime * physicalYangMillsMass = 33/20
```

be interpreted physically.

## Milestone 28 — Final physical Yang--Mills mass-gap theorem

**Status: OPEN.**

A final theorem must start from the actual interacting continuum Yang--Mills construction and conclude a strict non-vacuum spectral lower bound for the reconstructed physical Hamiltonian without circular numerical input.

It must preserve the distinctions

```text
finite Z2 cap 1/2
  != finite compact-Wilson intrinsic rate
  != unregularized statewise OS log-decay limit
  != continuum defect coercivity
  != physicalYangMillsMass
  != normalized 33/20 endpoint.
```

---

# Safest additive next packages

Two fronts are now mature enough for focused work and should remain logically separate.

## Package A — OS long-time decay to spectral mass

Preferred order:

```text
1. expose or reuse the exact physical semigroup <-> Hamiltonian spectral-calculus bridge;
2. represent the nonzero-state autocorrelation through its scalar spectral measure;
3. identify asymptotic log decay with the bottom of the spectral support seen by that state;
4. derive sampling-step independence from that common spectral quantity rather than assuming it;
5. compare the statewise bottom with the existing variational physical-mass interface;
6. state strict positivity only after a genuine spectral-gap/model theorem supplies it.
```

This package should not inject `33/20` or any desired positive constant into the asymptotic theorem.

## Package B — actual Wilson same-root realization

Preferred order:

```text
1. construct the cross-scale normalized-trace-power bounded-continuous physical observables;
2. prove exact same-root finite readout identities;
3. prove the needed gauge-invariant and positive-time membership properties;
4. discharge the #1670/#1671-#1675 readout premises;
5. identify the rational path-law two-point surface with the actual physical OS two-point surface where the roots coincide;
6. then compose with the already integrated reconstructed-excitation and reflection/Schwinger infrastructure.
```

The two packages can later meet at the physical state used for the spectral/log-decay theorem.

---

# Anti-goals

Do not:

- claim the Clay Millennium problem is solved before the model-facing continuum construction is complete;
- identify finite `Z₂` with compact `SU(2)` / `SU(N)` continuum Yang--Mills;
- identify finite coercivity `1/2` with the physical Yang--Mills mass;
- claim the former #1670 Draft frontier is still current — #1670 is merged;
- replace actual positive-time readout construction by global pullback surjectivity or multiplicativity;
- infer full real-path continuum field theory merely from rational path-law stationarity;
- infer continuum OS positivity merely from finite Gibbs reflection invariance;
- infer same-root OS reconstruction from a topological extension theorem alone;
- keep a fixed positive `epsilon` and interpret its long-time regularized effective-mass limit as a positive mass — that limit is proved to be zero;
- infer strict positivity of `m_infinity,h` from nonnegativity;
- identify `m_infinity,h` with `physicalYangMillsMass` before the spectral/variational bridge is proved;
- replace the moving-time `o(a_n)` requirement by ordinary fixed-time convergence;
- tune R4 coefficients or reference time to force `33/20`;
- identify static Wilson `A†A` with Euclidean time evolution.

# Completion criterion

The program reaches a final physical mass-gap theorem only when the same-root construction chain is closed:

```text
actual finite compact Wilson roots
  -> controlled continuum interacting Yang--Mills state
  -> continuum reflection-positive OS reconstruction
  -> physical Hilbert space and Hamiltonian from that same root
  -> non-vacuum spectral mass > 0
  -> finite-to-continuum and observable compatibility
  -> independent physical normalization
  -> optional exact normalized endpoint.
```

Until then, the repository should continue to advertise the strongest theorem actually integrated while keeping every remaining model-facing premise explicit.
