# MGAP4D Roadmap

This roadmap records the current proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-08-22 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

and the latest theorem-bearing checkpoint represented by this document is

```text
PR #2006
formal: record high-beta Dobrushin no-go
merge SHA:
d1d0d098771c55b906ea689e6af0b55d5b1f5aa4
```

The public `main` branch is a landing surface. Only results merged into the authoritative theorem carrier count as current theorem status.

The roadmap has changed materially since the earlier OS-reconstruction and same-root-coercivity checkpoints:

> **The main analytic frontier is now the derivation of a scale-uniform shared-boundary `L²` Poincaré / spectral-gap estimate for the actual finite Wilson transfer operator.**
>
> The repository already contains the machinery that converts such an estimate into finite vacuum-sector decay and then into a continuum Hamiltonian lower bound. The estimate itself is still model-facing and must not be replaced by a certificate assumption in the final proof.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated infrastructure** — implication machinery is formalized, but a model-facing input remains.
- **Conditional** — theorem is correct under an explicit hypothesis not yet derived from the intended physical scaling.
- **Open now** — immediate constructive frontier.
- **Open downstream** — required after the current frontier.
- **Route closed / diagnostic only** — useful finite theorem or obstruction, but not the intended continuum mass-gap mechanism.

---

# Roadmap in one view

```text
A. ACTUAL WILSON -> SAME-ROOT SCALAR CONTINUUM -> OS HAMILTONIAN

finite periodic-even compact SU(N) Wilson Gibbs model                   [Integrated]
  -> finite Wilson reflection positivity / OS geometry                  [Integrated]
  -> primary rational-time scalar readout                               [Integrated]
  -> same-root Prokhorov continuum law on ℚ -> ℝ                       [Integrated]
  -> continuum cylinder OS positivity / reflection invariance           [Integrated]
  -> fixed-slot OS Hilbert spaces / directed limit                      [Integrated]
  -> rational contraction semigroup                                     [Integrated]
  -> real C₀ contraction semigroup                                       [Integrated]
  -> dense generator / graph-closed self-adjoint Hamiltonian            [Integrated]
  -> normalized vacuum Ω / complete Ω⊥ excitation sector                [Integrated]

B. FINITE STATIC COVARIANCE LANE

finite Wilson local variation comparison                               [Integrated]
  -> two-sided support localization                                     [Integrated]
  -> finite-support variation profiles                                  [Integrated #1996]
  -> separated-support geometric covariance                             [Integrated #1995/#1997]
  -> midpoint Wilson-source bounded-continuous realization              [Integrated]
  -> factorial-distance covariance -> 0 under uniform rhoBar < 1        [Conditional]
  -> scalar weak-limit covariance transfer                              [Integrated #2005]
  -> continuum covariance = 0 under uniform rhoBar < 1                  [Conditional]
  -> high-beta incompatibility of current Dobrushin majorant             [Integrated #2006]

C. PHYSICAL MASS-GAP TRANSFER LANE

actual finite Wilson shared-boundary transfer K_(n,t)                   [model-facing]
  -> construct exact boundary-moment intertwining                       [OPEN NOW / verify existing carriers]
  -> prove scale-uniform boundary L² Poincaré defect                    [OPEN CORE]
  -> finite Wilson vacuum-orthogonal semigroup decay                    [Integrated infrastructure]
  -> common-carrier finite-to-continuum convergence                     [Integrated interface; model instantiation required]
  -> continuum Hamiltonian Rayleigh lower bound on Ω⊥                  [Integrated infrastructure]
  -> vacuum uniqueness / sub-mass spectral exclusion                    [Integrated infrastructure]
  -> positive physical mass gap on one same-root carrier                [OPEN downstream]

D. FULL 4D YANG--MILLS EXISTENCE LANE

selected scalar rational-time continuum process                        [Integrated]
  -> sufficiently rich continuum gauge-invariant field/state            [OPEN]
  -> full Euclidean/gauge/regularity package                            [OPEN]
  -> model-derived clustering / vacuum structure                        [OPEN]
  -> same physical Hamiltonian and excitation theory                    [OPEN]
  -> Clay-level existence + positive mass gap                           [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository operation rules:

```text
start ordinary proof PRs from the exact canonical SHA
start them as Draft
use the GitHub connector for repository operations
judge CI only when workflow / job / exact Lean step are all completed
never append commits to a queued or in_progress PR head
repair only after completed failure and a fresh exact-head check
keep changes additive / tighten-only
never introduce sorry / admit / axiom / placeholder constants
before Ready -> merge, re-check exact head/base/mergeability/reviews/threads
use normal merge with expected head pinned
record the actual merge SHA returned by GitHub
verify canonical is identical / ahead 0 / behind 0 after merge
start the next branch from that exact SHA
```

Claim discipline:

```text
finite static covariance != continuum physical mass gap
conditional ultralocality != desired physical exponential clustering
abstract gap-transfer interface != model-derived gap theorem
selected scalar continuum process != full 4D Yang--Mills field
internal spectral receipt/index != external mathematical completion
```

---

# Phase 1 — Actual finite compact `SU(N)` Wilson model

**Status: Integrated.**

The finite root uses the actual periodic-even compact special-unitary Wilson Gibbs law.

Integrated components include:

```text
oriented periodic lattice geometry
plaquettes and physical links
normalized Haar measure
Wilson action / Gibbs density / probability measure
reflection geometry
positive-half and boundary decompositions
finite Wilson reflection positivity / Gram identities
gauge-covariant plaquette holonomy
gauge-invariant normalized real traces
temporal translation and reflection covariance
finite support / plaquette-local support geometry
```

Permanent requirements:

- do not replace the interacting boundary marginal by Haar measure at nonzero coupling;
- do not convert a finite-model theorem into a continuum claim without an explicit transfer theorem;
- preserve the actual Wilson source through all same-root observable constructions.

---

# Phase 2 — Primary scalar rational path and same-root continuum law

**Status: Integrated.**

The constructive continuum lane uses the primary reflection-fixed spatial slice rather than treating the whole two-fixed-slice boundary readout as positive-half local.

Integrated route:

```text
primary reflection-fixed readout
  -> positive temporal path
  -> reflection completion from the same Wilson source
  -> primary plaquette normalized-trace scalarization
  -> path carrier ℚ -> ℝ
  -> tight finite pushforward laws
  -> Prokhorov subsequential continuum probability law
```

The resulting carrier is a genuine continuum observable process but is not the complete gauge connection on `ℝ⁴`.

---

# Phase 3 — Continuum OS positivity and fixed-slot Hilbert reconstruction

**Status: Integrated.**

The finite Wilson OS theorem has been transported to the same-root scalar continuum law.

Integrated results include:

```text
positive rational-cylinder OS reflection form
intrinsic path reflection invariance
symmetric positive-semidefinite OS bilinear forms
OS seminorm / null quotient
fixed-slot real Hilbert completion
isometric slot inclusions
directed family of Hilbert sectors
algebraic direct limit
completed direct-limit Hilbert carrier
```

This phase is no longer a current blocker.

---

# Phase 4 — Rational contraction and real strongly continuous OS semigroup

**Status: Integrated.**

The midpoint OS identity and shift-independent norm control yield rational-time contraction.

The development then constructs the maximal zero-time regular sector and extends the rational action canonically to `NNReal` time.

Integrated result:

```text
T_0 = I
T_s T_t = T_(s+t)
‖T_t x‖ <= ‖x‖
T_t x -> x as t -> 0+
```

with OS symmetry and positivity retained.

---

# Phase 5 — Generator, closed Hamiltonian, Yosida recovery, and vacuum

**Status: Integrated.**

Integrated chain:

```text
right difference-quotient generator A_OS
H_OS = -A_OS
dense generator domain
nonnegative quadratic form
graph closure as a Mathlib LinearPMap
positive-shift range theorem
self-adjoint graph-closed Hamiltonian H̄
positive resolvent family
Yosida contractions
bounded exponential approximants
strong recovery of the original OS semigroup
exact generator / H̄ domain identification
```

The literal empty-slot constant-one cylinder gives the same-root vacuum `Ω`.

Integrated vacuum/excitation facts:

```text
‖Ω‖ = 1
T_t Ω = Ω
H̄ Ω = 0
Ω⊥ is complete
T_t preserves Ω⊥
H̄ preserves the exact excitation-domain intersection
```

This phase supplies the correct carrier on which a positive lower bound must ultimately be derived.

---

# Phase 6 — Two-sided finite covariance localization

**Status: Integrated.**

The earlier one-sided covariance comparison could not produce spatial clustering because sources adjacent to one observable retained order-one contributions. The remedy was not a sharper Neumann kernel alone but a **two-sided support-localized covariance comparison**.

The integrated finite result now has the schematic form

```text
|Cov(F,O)|
  <= geometric(distance(S,T))
     * local_variation(F,T)
     * local_variation(O,S)
```

for plaquette-locally separated supports.

For the current special-unitary active-TV majorant

```text
q(beta) = (exp(4 * beta) - 1) / (exp(4 * beta) + 1),
```

the explicit geometric factor is based on

```text
rho(beta) = 18 * q(beta).
```

Under `rho(beta) < 1`, the finite Wilson covariance decays geometrically in the discrete separation.

---

# Phase 7 — Finite-support observable interface and actual midpoint sources

**Status: Integrated.**

PR #1996 removes proof-engineering friction from the local covariance theorem: a bounded-continuous observable depending only on a finite support automatically gets a link-variation profile with variation

```text
2 * ‖O‖ on the support
0 outside the support.
```

PR #1997 packages this into a direct separated-finite-support covariance interface.

Subsequent canonical work connects the actual midpoint left/right Wilson-source observables to bounded-continuous functions and exact finite support receipts, so the static geometric covariance theorem applies to the same observables used in the scalar continuum path construction.

Completion criterion: satisfied at finite volume.

---

# Phase 8 — Factorial physical separation and covariance weak-limit transfer

**Status: Integrated transfer, conditional decay hypothesis.**

For a fixed positive rational physical separation, the number of lattice steps between the midpoint supports grows as the lattice spacing vanishes.

If there exists one `rhoBar < 1` such that eventually

```text
18 * q(beta n) <= rhoBar,
```

then the finite geometric covariance bound tends to zero.

PR #2005 closes the representation/weak-limit gap:

```text
actual finite Wilson midpoint covariance
  = covariance of fixed bounded-continuous tests on ℚ -> ℝ
  -> weak convergence of left/right/product expectations
  -> convergence to continuum scalar path covariance.
```

Hence the uniform-ratio hypothesis forces the continuum midpoint covariance to be exactly zero.

Interpretation:

> this is **conditional ultralocality**. It is intentionally not advertised as the physical clustering theorem required for Yang--Mills mass gap.

---

# Phase 9 — High-beta diagnostic for the Dobrushin route

**Status: Integrated; current Dobrushin route closed as a high-beta mass-gap mechanism.**

PR #2006 proves

```text
q(beta) -> 1                 as beta -> +∞
18 * q(beta) -> 18           as beta -> +∞.
```

Therefore, whenever a concrete scaling has

```text
beta n -> +∞,
```

the eventual finite threshold

```text
18 * q(beta n) < 1
```

and every scale-independent bound

```text
18 * q(beta n) <= rhoBar < 1
```

are impossible.

Roadmap consequence:

```text
DO NOT spend the next proof sequence trying to promote the present active-TV
Dobrushin majorant into the physical continuum mass-gap estimate.
```

The finite covariance theorem remains useful as a correct high-temperature static result and as a diagnostic testbed.

---

# Phase 10 — Identify the real quantitative gap input

**Status: Integrated infrastructure; model estimate open.**

The physical OS gap-transfer machinery makes the remaining analytic input explicit.

At the finite approximating Hilbert level, the desired model-specific conclusion is a common decay function `d(t)` satisfying

```text
‖T^(n)_t phi‖ <= d(t) * ‖phi‖
```

for every scale `n` and every finite-volume vector orthogonal to the normalized vacuum, together with

```text
t⁻¹ * (1 - d(t)) -> m > 0
```

as `t -> 0+`.

The existing boundary route reduces this further to a shared-boundary `L²` estimate.

---

# Phase 11 — Construct the actual shared-boundary transfer operator

**Status: Open now / inspect and tighten existing carriers.**

The current certificate interfaces contain a continuous linear map

```text
K_(n,t) : BoundaryL2(n) ->L[ℝ] BoundaryL2(n)
```

and an intertwining identity between the boundary moment of a centered positive-time observable and the boundary moment after half-time translation.

The next implementation work should proceed in this order:

```text
1. trace the existing finite boundary kernel / conditional-expectation carriers;
2. define K_(n,t) from the actual Wilson finite measure whenever not already concrete;
3. prove boundedness and the continuous-linear-map packaging;
4. derive the boundaryMoment_intertwining theorem from the finite Wilson geometry;
5. remove corresponding certificate fields whenever theorem derivations exist.
```

The objective is to ensure that the gap package consumes a genuinely constructed finite Wilson operator rather than an opaque operator parameter.

---

# Phase 12 — Prove a scale-uniform boundary `L²` Poincaré / spectral-gap estimate

**Status: OPEN CORE.**

The cleanest target currently exposed by the exponential boundary certificate is:

```text
∃ m > 0, ∀ n t v,
  (1 - exp (-m * t)) * ‖v‖²
    <= ‖v‖² - ‖K_(n,t) v‖².
```

The important features are:

```text
m is strictly positive;
m is independent of n;
the operator is the actual finite Wilson shared-boundary transfer;
the inequality is proved from the model rather than stored as a field.
```

Possible mathematical routes to investigate include, without presupposing success:

```text
finite-volume transfer-operator spectral analysis
Dirichlet-form / Poincaré inequality on the shared boundary
representation-theoretic decomposition of the compact gauge boundary kernel
comparison with a model-derived coercive quadratic form
reflection-positive transfer-matrix estimates
uniform finite-volume lower bounds stable under the chosen scaling
```

The route must be compatible with the actual coupling/continuum scaling. The high-temperature Dobrushin majorant is not a substitute for this estimate.

Completion criterion:

```text
a theorem builds the exponential boundary Poincaré certificate from actual
finite Wilson data with a strictly positive scale-independent m.
```

---

# Phase 13 — Finite vacuum-sector decay and continuum Rayleigh lower bound

**Status: Integrated infrastructure; waits on Phase 12 and concrete common-carrier data.**

Once the exponential boundary estimate is available, the existing chain gives

```text
boundary Poincaré defect
  -> boundary quadratic contraction
  -> boundary-moment contraction
  -> completed finite Wilson OS vacuum-orthogonal decay
  -> positive small-time slope
  -> finite-volume gap certificate.
```

The common-carrier transfer package then proves, on the continuum OS Hamiltonian domain,

```text
m * ‖psi‖² <= inner ℝ (H psi) psi
```

for `psi ⟂ Ω`.

Required tightening before final use:

```text
construct/verify the approximation maps from the actual same-root finite OS spaces;
construct/verify the isometric embeddings into the continuum carrier;
prove approximate_tendsto;
prove evolved_tendsto;
avoid treating these convergence fields as final physical assumptions.
```

---

# Phase 14 — Same-root spectral gap consequences

**Status: Open downstream, implication machinery largely integrated.**

After a genuine positive Rayleigh lower bound is established on the actual vacuum-orthogonal continuum Hamiltonian, close the consequences on the same carrier:

```text
strictly positive excitation infimum
vacuum uniqueness in the zero-energy sector
sub-mass resolvent and spectrum exclusion
uniform excitation semigroup decay
physical correlation-length consequences where justified
```

Do not import `33/20` or any other numerical value at this stage unless a theorem derives it from this exact Hamiltonian/model route.

---

# Phase 15 — Full four-dimensional continuum Yang--Mills carrier

**Status: Open downstream and essential for a Clay-level claim.**

The current same-root scalar process is not the entire four-dimensional Yang--Mills field.

Required future construction must provide a sufficiently rich continuum state/observable system with the appropriate combination of

```text
Euclidean covariance
local gauge-invariant observable algebra
gauge structure
reflection positivity
regularity / distributional control
clustering / vacuum structure
finite-Wilson approximation compatibility
nontriviality
```

and identify its physical OS/Hamiltonian reconstruction with the carrier on which the positive gap is proved.

---

# Phase 16 — Signed-spatial / glueball lane

**Status: Parallel; not the immediate blocker.**

Existing finite signed-spatial symmetry work provides substantial lattice geometry and configuration actions.

Still required before any glueball interpretation:

```text
full plaquette-holonomy covariance under the signed spatial group
observable representation decomposition
cubic irrep identification
continuum rotational/spin identification
nonzero overlap with the physical spectral sector
spectral mass statement on the final Hamiltonian
```

No glueball mass follows from spatial symmetry alone.

---

# Phase 17 — Exact-value lane

**Status: Separate / conditional.**

The repository contains an internal exact-value/spectral-atom route involving the normalized value `33/20`.

That route must remain logically separate from the constructive same-root mass-gap lane until explicit theorems identify:

```text
the physical Hamiltonian carrier
the normalization
the spectral infimum / atom
the relevant observable spectral weight
```

with the final Yang--Mills construction.

No documentation should present `33/20` as the established physical Yang--Mills mass gap merely because it appears in a separate formal spectral route.

---

# Immediate execution order

The next proof sequence should be:

```text
1. inspect the concrete finite Wilson shared-boundary kernel/transfer definitions;
2. eliminate avoidable abstract fields from the boundary-gap certificate path;
3. prove the exact boundary-moment intertwining for the constructed operator;
4. isolate the sharpest finite shared-boundary Dirichlet/Poincaré form;
5. seek a strictly positive n-uniform lower bound compatible with continuum scaling;
6. instantiate the exponential boundary L² Poincaré certificate;
7. instantiate the actual finite vacuum-gap certificate;
8. close the common-carrier finite-to-continuum convergence fields;
9. derive the same-root continuum Ω⊥ Rayleigh lower bound;
10. only then promote to spectral-gap / clustering consequences.
```

A failed attempt at Step 5 should be treated as mathematical information: identify the scaling obstruction or missing renormalized estimate rather than hiding it behind a stronger assumption.

---

# Current stop conditions

The project must continue to stop short of a Clay-level claim while any of the following remain unproved on one coherent model-derived carrier:

```text
scale-uniform positive finite Wilson transfer/Poincaré gap
actual finite-to-continuum gap convergence
positive continuum excitation lower bound
sufficiently rich four-dimensional continuum Yang--Mills field/state
required Euclidean/gauge/regularity/clustering properties
identification of the final physical Hamiltonian and its gap
```

The purpose of the roadmap is to keep those boundaries visible while allowing each finite, continuum, OS, and spectral component to be strengthened rigorously and incrementally.
